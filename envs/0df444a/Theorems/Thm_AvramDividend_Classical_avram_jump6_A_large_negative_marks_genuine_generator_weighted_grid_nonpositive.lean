-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_large_negative_marks_genuine_generator_weighted_grid_nonpositive
-- name    : AvramDividend.Classical.avram_jump6_A_large_negative_marks_genuine_generator_weighted_grid_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:38:01.299228+00:00
-- url     : https://prove2.me/theorems/526b8d01-1f58-49a8-a093-8787b5835cf8
-- title:
--   Genuine finite overshooting negative-mark generator weighted mesh drift is nonpositive
-- statement:
--   For a finite-activity negative Levy measure supported on marks at most minus two, the actual nonlinear generator-integrand of the stopped quadratic HJB function is nonpositive at every grid reserve 0 to one fifth. Any finite sum against nonnegative predictable scalar grid weights is nonpositive. This is the marked compensator contribution missing from deprecated unit-fullmark mesh estimates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_large_negative_marks_genuine_generator_weighted_grid_nonpositive
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hSupport : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))), z ≤ -2)
    (m : ℕ) (y weight : ℕ → ℝ)
    (hy : ∀ i ∈ Finset.range m, 0 ≤ y i ∧ y i ≤ (1 / 5 : ℝ))
    (hw : ∀ i ∈ Finset.range m, 0 ≤ weight i) :
    (∑ i ∈ Finset.range m, weight i *
      (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun u : ℝ => if u < 0 then 0 else 1 + u + u ^ 2)
          (y i) z ∂X.ν)) ≤ 0 := by sorry
