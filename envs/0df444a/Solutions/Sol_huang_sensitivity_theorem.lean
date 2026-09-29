-- Prove2me | solution 1 for huang_sensitivity_theorem
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-04-23T04:03:10.37097+00:00
-- url     : https://prove2.me/submissions/cfce71a5-4aa3-4613-89ee-2550116bc79f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_cauchy_interlacing_sorted
import Theorems.Thm_huang_matrix_spectrum_sorted
import Theorems.Thm_max_degree_ge_lambda_max
import Theorems.Thm_huangMatrix_entry_abs
import Definitions.Def_Hypercube
import Definitions.Def_huangMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sketch — Theorem 1.1 via Huang's three lemmas

Huang-style decomposition of `huang_sensitivity_theorem`:

  body uses  `max_degree_ge_lambda_max`        (Lemma 2.3 — generic spectral bound)
             `cauchy_interlacing_sorted`       (Lemma 2.1 — sorted interlace)
             `huang_matrix_spectrum_sorted`    (Lemma 2.2 — full ±√n spectrum)

The three children live in `Theorems/` with `sorry` bodies; this sketch combines
them into a **sorry-free** proof of `huang_sensitivity_theorem`.
-/

open scoped Classical

theorem solution :
    ∀ (n : ℕ), 0 < n → ∀ (S : Finset (Fin n → Bool)), 2 ^ (n - 1) < S.card →
      ∃ v ∈ S, n ≤ Hypercube.degreeIn n S v ^ 2 := by
  intro n hn S hS
  -- Nonempty S (from 2^(n-1) < S.card and 2^(n-1) ≥ 1 when n ≥ 1)
  have hS_ne : S.Nonempty := Finset.card_pos.mp (by
    have : 0 < 2 ^ (n - 1) := pow_pos (by norm_num : (0 : ℕ) < 2) _
    omega)
  -- Card facts
  have hcardα : Fintype.card (Fin n → Bool) = 2 ^ n := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hcardβ : Fintype.card (↥S : Type) = S.card := Fintype.card_coe S
  -- Upper bound on S.card
  have hS_le : S.card ≤ 2 ^ n := by
    rw [← hcardα, ← hcardβ]; exact Fintype.card_le_of_injective _ Subtype.coe_injective
  -- 2^n - S.card < 2^(n-1)  (key arithmetic used for Lemma 2.2 lookup)
  have h_pos_pow_sub_one : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel hn).symm]
    rw [pow_succ]; ring
  have h_pos_gap : 2 ^ n - S.card < 2 ^ (n - 1) := by omega
  -- The principal submatrix indexed by ↥S, and its Hermitian witness
  set A := huangMatrix n with hA_def
  set hA := huangMatrix_is_hermitian n with hA_def'
  set f : ↥S ↪ (Fin n → Bool) := Function.Embedding.subtype _ with hf_def
  set B := A.submatrix (f : ↥S → _) (f : ↥S → _) with hB_def
  set hB := hA.submatrix (f : ↥S → _) with hB_def'
  -- Nonempty S means Nonempty ↥S
  have : Nonempty (↥S : Type) := hS_ne.to_subtype
  ---------------------------------------------------------------------------
  -- Step 1: Upper bound λ_max(B) ≤ some deg via Lemma 2.3
  ---------------------------------------------------------------------------
  -- Entries of B lie in {-1, 0, 1} because huangMatrix entries do.
  have h_entries : ∀ u v : ↥S, B u v = -1 ∨ B u v = 0 ∨ B u v = 1 := by
    intro u v
    have habs : |huangMatrix n u.val v.val| = if Hypercube.Adj n u.val v.val then 1 else 0 :=
      huangMatrix_entry_abs n u.val v.val
    change huangMatrix n u.val v.val = _ ∨ _ ∨ _
    by_cases hadj : Hypercube.Adj n u.val v.val
    · rw [if_pos hadj] at habs
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
    · rw [if_neg hadj] at habs
      exact Or.inr (Or.inl (abs_eq_zero.mp habs))
  -- Zero pattern: B[u,v] = 0 whenever u, v ∈ S are non-adjacent in Q_n.
  have h_zero : ∀ u v : ↥S, ¬ (Hypercube.Adj n u.val v.val) → B u v = 0 := by
    intro u v hne
    have habs := huangMatrix_entry_abs n u.val v.val
    rw [if_neg hne] at habs
    change huangMatrix n u.val v.val = 0
    exact abs_eq_zero.mp habs
  -- Apply Lemma 2.3
  obtain ⟨v, h_le⟩ := max_degree_ge_lambda_max (V := ↥S) hB h_entries
    (fun u v : ↥S => Hypercube.Adj n u.val v.val) h_zero
  -- The filter cardinality equals Hypercube.degreeIn n S v.val.
  have h_filter_eq :
      ((Finset.univ : Finset (↥S)).filter
          fun u : ↥S => Hypercube.Adj n u.val v.val).card =
        Hypercube.degreeIn n S v.val := by
    unfold Hypercube.degreeIn
    refine Finset.card_bij (fun (u : ↥S) _ => u.val) ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      simp [Finset.mem_filter, u.property, hu]
    · intro u _ u' _ h; exact Subtype.ext h
    · intro x hx
      simp only [Finset.mem_filter] at hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      simp [Finset.mem_filter, hx.2]
  -- Combine: λ_max(B) ≤ deg_S(v.val)
  have h_upper : hB.eigenvalues₀ ⟨0, by rw [hcardβ]; exact Finset.card_pos.mpr hS_ne⟩
      ≤ (Hypercube.degreeIn n S v.val : ℝ) := by
    rw [← h_filter_eq]; exact_mod_cast h_le
  ---------------------------------------------------------------------------
  -- Step 2: Lower bound λ_max(B) ≥ √n via Cauchy sorted + Huang spectrum
  ---------------------------------------------------------------------------
  have h_interlace :=
    cauchy_interlacing_sorted (α := (Fin n → Bool)) (β := (↥S : Type))
      hA f ⟨0, by rw [hcardβ]; exact Finset.card_pos.mpr hS_ne⟩
  have h_shift_lt : Fintype.card (Fin n → Bool) - Fintype.card (↥S : Type) < 2 ^ (n - 1) := by
    rw [hcardα, hcardβ]; exact h_pos_gap
  have h_spec :
      hA.eigenvalues₀
        ⟨(0 : ℕ) + (Fintype.card (Fin n → Bool) - Fintype.card (↥S : Type)), by
          have hle : Fintype.card (↥S : Type) ≤ Fintype.card (Fin n → Bool) :=
            Fintype.card_le_of_injective _ f.injective
          have : (0 : ℕ) < Fintype.card (↥S : Type) := by
            rw [hcardβ]; exact Finset.card_pos.mpr hS_ne
          omega⟩ = Real.sqrt n := by
    have h_index_lt : (0 : ℕ) + (Fintype.card (Fin n → Bool) - Fintype.card (↥S : Type))
        < 2 ^ (n - 1) := by simpa using h_shift_lt
    have hA_index : (0 : ℕ) + (Fintype.card (Fin n → Bool) - Fintype.card (↥S : Type))
        < Fintype.card (Fin n → Bool) := by
      rw [hcardα]; omega
    rw [huang_matrix_spectrum_sorted n hn
      ⟨(0 : ℕ) + (Fintype.card (Fin n → Bool) - Fintype.card (↥S : Type)), hA_index⟩]
    rw [if_pos h_index_lt]
  have h_lower : (Real.sqrt n : ℝ) ≤ hB.eigenvalues₀
      ⟨0, by rw [hcardβ]; exact Finset.card_pos.mpr hS_ne⟩ := by
    calc (Real.sqrt n : ℝ) = _ := h_spec.symm
      _ ≤ _ := h_interlace
  ---------------------------------------------------------------------------
  -- Step 3: chain √n ≤ deg, square to get n ≤ deg²
  ---------------------------------------------------------------------------
  have h_sqrt_le : Real.sqrt n ≤ (Hypercube.degreeIn n S v.val : ℝ) :=
    le_trans h_lower h_upper
  refine ⟨v.val, v.property, ?_⟩
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hsq : Real.sqrt n * Real.sqrt n ≤
      (Hypercube.degreeIn n S v.val : ℝ) * (Hypercube.degreeIn n S v.val : ℝ) :=
    mul_self_le_mul_self (Real.sqrt_nonneg _) h_sqrt_le
  rw [Real.mul_self_sqrt hn_nn] at hsq
  have hfinal : (n : ℝ) ≤ (Hypercube.degreeIn n S v.val : ℝ) ^ 2 := by nlinarith [hsq]
  exact_mod_cast hfinal
