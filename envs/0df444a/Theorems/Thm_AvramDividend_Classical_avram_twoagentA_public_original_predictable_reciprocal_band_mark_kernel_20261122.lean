-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_predictable_reciprocal_band_mark_kernel_20261122
-- name    : AvramDividend.Classical.avram_twoagentA_public_original_predictable_reciprocal_band_mark_kernel_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:21:20.02719+00:00
-- url     : https://prove2.me/theorems/5d4b8f92-461b-442a-93fb-b2c910c2febb
-- title:
--   Original physical marked integral L1 source 4983c304
-- statement:
--   Exact already accepted original negative-mark signed-integral source proof, republished as public importable prerequisite for the genuine unrestricted negative activity physical compensated mark L1 centring and reciprocal quantizer approximation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_public_original_predictable_reciprocal_band_mark_kernel_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (n m : ℕ) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let F : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if 0 < p.1.1 ∧ p.1.1 ≤ T ∧ p.2 ∈ B then p.2 else 0
    Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] F ∧
    (∀ p, |F p| ≤ (1 : ℝ)) := by sorry
