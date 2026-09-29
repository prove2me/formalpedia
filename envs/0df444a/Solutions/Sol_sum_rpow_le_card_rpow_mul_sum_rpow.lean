-- Prove2me | solution 1 for sum_rpow_le_card_rpow_mul_sum_rpow
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-25T02:41:40.964081+00:00
-- url     : https://prove2.me/submissions/f0c8827c-b0b4-4398-a1de-943a010a1a2f

import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.Basic

open scoped BigOperators

theorem solution {N : ℕ}
    (σ : Fin N → ℝ) (hσ : ∀ k, 0 ≤ σ k) (q s : ℝ) (hq : 0 < q) (hqs : q ≤ s) :
    (∑ k, (σ k) ^ q) ≤ (N : ℝ) ^ (1 - q / s) * (∑ k, (σ k) ^ s) ^ (q / s) := by
  classical
  have hs : 0 < s := lt_of_lt_of_le hq hqs
  set p : ℝ := s / q with hp
  have hp1 : 1 ≤ p := by rw [hp, le_div_iff₀ hq]; linarith
  have hf0 : ∀ k, (0:ℝ) ≤ (σ k) ^ q := fun k => Real.rpow_nonneg (hσ k) q
  have hHolder := Real.inner_le_weight_mul_Lp_of_nonneg (Finset.univ : Finset (Fin N)) hp1
    (fun _ => (1:ℝ)) (fun k => (σ k) ^ q) (fun _ => zero_le_one) hf0
  simp only [one_mul] at hHolder
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hHolder
  have hfp : ∀ k, ((σ k) ^ q) ^ p = (σ k) ^ s := by
    intro k
    rw [← Real.rpow_mul (hσ k)]
    congr 1
    rw [hp]; field_simp
  simp only [hfp] at hHolder
  have hpinv : p⁻¹ = q / s := by rw [hp, inv_div]
  rw [hpinv] at hHolder
  exact hHolder
