-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_discounted_genuine_negative_mark_mesh_generator_nonpositive
-- name    : AvramDividend.Classical.avram_jump6_A_discounted_genuine_negative_mark_mesh_generator_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:14:48.084003+00:00
-- url     : https://prove2.me/theorems/06353082-6d1f-4c0b-9dcc-13f881af93f8
-- title:
--   Physical discounted overshooting negative-mark finite mesh HJB drift is nonpositive
-- statement:
--   Every original finite-activity genuinely negative mark generator contribution supported on ruin overshoots remains nonpositive when integrated on a finite stochastic grid against nonnegative predictable scalar weights and positive exponential discount. This is exactly the nonlinear mark compensator sign retained by the physical mixed Gaussian/jump Ito cash ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_discounted_genuine_negative_mark_mesh_generator_nonpositive
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hSupport : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))), z ≤ -2)
    (q : ℝ) (m : ℕ) (t : ℕ → ℝ≥0) (y weight : ℕ → ℝ)
    (hy : ∀ i ∈ Finset.range m, 0 ≤ y i ∧ y i ≤ (1 / 5 : ℝ))
    (hw : ∀ i ∈ Finset.range m, 0 ≤ weight i) :
    (∑ i ∈ Finset.range m, Real.exp (-(q * (t i : ℝ))) * weight i *
      (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun u : ℝ => if u < 0 then 0 else 1 + u + u ^ 2)
          (y i) z ∂X.ν)) ≤ 0 := by sorry
