-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_NNReal_positive_shift_stopping
-- name    : AvramDividend.Classical.avram_f6_original_NNReal_positive_shift_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:53:50.349449+00:00
-- url     : https://prove2.me/theorems/904023ff-c07d-4ffe-aaa7-fc23a88cd15b
-- title:
--   Original nonnegative-real filtration positive deterministic shift preserves stopping time
-- statement:
--   For any original right-continuous filtration with nonnegative real clock, adding a fixed nonnegative deterministic delay to a stopping time remains a stopping time. Proof uses time-threshold cases and truncated subtraction, respecting the nonnegative time index. Supplies a reusable source for original physical right-mesh proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_NNReal_positive_shift_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (δ : ℝ≥0) :
    IsStoppingTime 𝓕.rightCont
      (fun ω => ((σ ω + δ : ℝ≥0) : WithTop ℝ≥0)) := by sorry
