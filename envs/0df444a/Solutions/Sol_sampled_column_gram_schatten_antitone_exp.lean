-- Prove2me | solution 1 for sampled_column_gram_schatten_antitone_exp
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-23T21:40:58.373669+00:00
-- url     : https://prove2.me/submissions/2fa1c9e2-6fad-4a7c-8ce0-e44fc03c0c4d

import Definitions.Def_matrix_completion_gram_schatten
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Bridge (d), column half — `sampled_column_gram_schatten_antitone_exp`. Symmetric partner of the
row version; both are needed for the `max(rowGS, colGS)` RHS of Core A general-q.
Source: Hardy–Littlewood–Pólya, *Inequalities* §2.10; CR2009 (arXiv:0805.4471) §6.1.
-/

open scoped BigOperators

namespace MatrixCompletion

/-- Power-mean / ℓ_p monotonicity for a nonnegative finite vector (reused from F3). -/
theorem lp_antitone_exp {N : ℕ} (σ : Fin N → ℝ) (hσ : ∀ k, 0 ≤ σ k)
    (q q' : ℝ) (hq : 1 ≤ q) (hqq' : q ≤ q') :
    (∑ k, (σ k) ^ q') ^ q'⁻¹ ≤ (∑ k, (σ k) ^ q) ^ q⁻¹ := by
  have hq0 : (0:ℝ) < q := lt_of_lt_of_le one_pos hq
  have hq'0 : (0:ℝ) < q' := lt_of_lt_of_le hq0 hqq'
  set Sq : ℝ := ∑ k, (σ k) ^ q with hSq
  set Sq' : ℝ := ∑ k, (σ k) ^ q' with hSq'
  have hSq_nonneg : 0 ≤ Sq := Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hσ k) q
  have hSq'_nonneg : 0 ≤ Sq' := Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hσ k) q'
  set A : ℝ := Sq ^ q⁻¹ with hA
  have hA_nonneg : 0 ≤ A := Real.rpow_nonneg hSq_nonneg _
  rw [Real.rpow_inv_le_iff_of_pos hSq'_nonneg hA_nonneg hq'0]
  rcases eq_or_lt_of_le hA_nonneg with hA0 | hApos
  · have hA0' : A = 0 := hA0.symm
    have hSq_zero : Sq = 0 := by
      by_contra hne
      have hSqpos : 0 < Sq := lt_of_le_of_ne hSq_nonneg (Ne.symm hne)
      have hpos : 0 < A := Real.rpow_pos_of_pos hSqpos _
      rw [hA0'] at hpos; exact lt_irrefl _ hpos
    have hterm_zero : ∀ k, σ k = 0 := by
      intro k
      have hle : (σ k) ^ q ≤ 0 := by
        have hsingle := Finset.single_le_sum (f := fun j => (σ j) ^ q)
          (fun j _ => Real.rpow_nonneg (hσ j) q) (Finset.mem_univ k)
        rw [← hSq, hSq_zero] at hsingle; exact hsingle
      have hge : 0 ≤ (σ k) ^ q := Real.rpow_nonneg (hσ k) q
      have hrpow0 : (σ k) ^ q = 0 := le_antisymm hle hge
      by_contra hσne
      have hσpos : 0 < σ k := lt_of_le_of_ne (hσ k) (Ne.symm hσne)
      have hp : 0 < (σ k) ^ q := Real.rpow_pos_of_pos hσpos _
      rw [hrpow0] at hp; exact lt_irrefl _ hp
    have hSq'_zero : Sq' = 0 := by
      rw [hSq']; refine Finset.sum_eq_zero fun k _ => ?_
      rw [hterm_zero k]; exact Real.zero_rpow (ne_of_gt hq'0)
    rw [hSq'_zero, hA0']
    exact le_of_eq (Real.zero_rpow (ne_of_gt hq'0)).symm
  · have hAq : A ^ q = Sq := by
      rw [hA, ← Real.rpow_mul hSq_nonneg, inv_mul_cancel₀ (ne_of_gt hq0), Real.rpow_one]
    have hσ_le_A : ∀ k, σ k ≤ A := by
      intro k
      have hsingle : (σ k) ^ q ≤ Sq := by
        have := Finset.single_le_sum (f := fun j => (σ j) ^ q)
          (fun j _ => Real.rpow_nonneg (hσ j) q) (Finset.mem_univ k)
        rw [← hSq] at this; exact this
      rw [← hAq] at hsingle
      by_contra hlt
      have hAlt : A < σ k := not_le.mp hlt
      have hgt : A ^ q < (σ k) ^ q := Real.rpow_lt_rpow hA_nonneg hAlt hq0
      exact absurd hsingle (not_le.mpr hgt)
    have hqq'sub : 0 ≤ q' - q := by linarith
    have hterm : ∀ k, (σ k) ^ q' ≤ (σ k) ^ q * A ^ (q' - q) := by
      intro k
      have hsplit : (σ k) ^ q' = (σ k) ^ q * (σ k) ^ (q' - q) := by
        rw [← Real.rpow_add' (hσ k) (y := q) (z := q' - q) (by
              have hsum : q + (q' - q) = q' := by ring
              rw [hsum]; exact ne_of_gt hq'0)]
        congr 1; ring
      rw [hsplit]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hσ k) q)
      exact Real.rpow_le_rpow (hσ k) (hσ_le_A k) hqq'sub
    calc Sq' = ∑ k, (σ k) ^ q' := hSq'
      _ ≤ ∑ k, ((σ k) ^ q * A ^ (q' - q)) := Finset.sum_le_sum fun k _ => hterm k
      _ = (∑ k, (σ k) ^ q) * A ^ (q' - q) := by rw [← Finset.sum_mul]
      _ = Sq * A ^ (q' - q) := by rw [← hSq]
      _ = A ^ q * A ^ (q' - q) := by rw [hAq]
      _ = A ^ q' := by rw [← Real.rpow_add hApos]; ring_nf

end MatrixCompletion

open MatrixCompletion

/-- Bridge (d), column half: the per-column sampled Gram-Schatten ℓ_q quantity is antitone in
the exponent. For `1 ≤ q ≤ q'`,
`sampledColumnGramSchatten Ω p X q' ≤ sampledColumnGramSchatten Ω p X q`. -/
theorem solution {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (hp : 0 ≤ p) (X : MatrixCompletion.RealMatrix n1 n2) (q q' : Real)
    (hq : 1 ≤ q) (hqq' : q ≤ q') :
    MatrixCompletion.sampledColumnGramSchatten Omega p X q'
      ≤ MatrixCompletion.sampledColumnGramSchatten Omega p X q := by
  unfold MatrixCompletion.sampledColumnGramSchatten
  exact MatrixCompletion.lp_antitone_exp
    (fun j => p⁻¹ * Real.sqrt (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0))
    (fun j => mul_nonneg (inv_nonneg.mpr hp) (Real.sqrt_nonneg _))
    q q' hq hqq'

#print axioms solution
