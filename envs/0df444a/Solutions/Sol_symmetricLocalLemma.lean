-- Prove2me | solution 1 for symmetricLocalLemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:44:19.972008+00:00
-- url     : https://prove2.me/submissions/a2f286a5-eab0-441a-9a1c-4fa46135f558

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma
import Theorems.Thm_localLemma
import Theorems.Thm_add_one_inv_pow_le_exp

set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {A : ι → Set Ω} {N : ι → Finset ι} {x : ι → ℝ} {i j : ι} {S T : Finset ι}
open Finset
theorem _root_.solution [Finite ι] [IsProbabilityMeasure P] (hA : ∀ i, MeasurableSet (A i))
    {d : ℕ} (hd : d ≠ 0) {p : ℝ} (h : lopsidedCondition P A N) (hAp : ∀ i, P.real (A i) ≤ p)
    (hN : ∀ i, #(N i) ≤ d)
    (hpd : Real.exp 1 * p * (d + 1) ≤ 1) :
    0 < P.real (⋂ i, (A i)ᶜ) := by
  have := Fintype.ofFinite ι
  let x (i : ι) : ℝ := (d + 1)⁻¹
  have hx₀ (i : ι) : 0 ≤ x i := by positivity
  have hx₁ (i : ι) : x i < 1 := inv_lt_one_of_one_lt₀ (by simp [hd, pos_iff_ne_zero])
  suffices hx : ∀ i, P.real (A i) ≤ x i * ∏ j ∈ N i, (1 - x j) from
    (localLemma hA hx₀ (fun i ↦ (hx₁ i).le) h hx).trans_lt' (prod_pos (by simp [hx₁]))
  intro i
  calc
    P.real (A i) ≤ p := hAp _
    _ ≤ (d + 1 : ℝ)⁻¹ * (Real.exp 1)⁻¹ := by
      rw [← mul_inv, ← one_div, le_div_iff₀]
      · linear_combination hpd
      · positivity
    _ ≤ (d + 1 : ℝ)⁻¹ * (1 + (↑d)⁻¹)⁻¹ ^ d := by grw [inv_pow, add_one_inv_pow_le_exp]
    _ = (d + 1 : ℝ)⁻¹ * (1 - (d + 1 : ℝ)⁻¹) ^ d := by
      congr! 2
      simp [field]
    _ ≤ (d + 1 : ℝ)⁻¹ * ∏ j ∈ N i, (1 - (d + 1 : ℝ)⁻¹) := by
      simp only [prod_const]
      gcongr _ * ?_
      apply pow_le_pow_of_le_one _ _ (by grind)
      · simpa using (hx₁ i).le
      · simpa [x] using hx₀ i
    _ = x i * ∏ j ∈ N i, (1 - x j) := rfl
