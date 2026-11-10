-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_first_negative_jump_clipped_finite_stopping
-- name    : AvramDividend.Classical.avram_bv_zero13_original_first_negative_jump_clipped_finite_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:12:40.534999+00:00
-- url     : https://prove2.me/theorems/9170abde-5ac5-4f65-a389-8e3201d267f4
-- title:
--   Actual original first negative jump clipped to finite horizon is bounded right-continuous stopping clock
-- statement:
--   Given the public Proved original first physical strictly negative source jump stopping time in WithTop nonnegative reals, clip at an arbitrary finite horizon and use untopD to obtain a genuinely nonnegative-real-valued clock, bounded by that horizon and measurable at every original right-continuous filtration sublevel. This is the exact finite stopping input required by existing original stopped-future zero-jump hazard and stopped-history factorisation theorems. Valid even with infinite first jump and zero horizon; preserves physical source and filtration.
-- source:
--   Necessary root-connected original source bridge: Proved 00cb3771 and 004fdd62 require a finite NNReal-valued stopping time, whereas the physical first negative jump 48fcb9f3 has WithTop NNReal codomain.

import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_first_negative_jump_inf_isStoppingTime

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_first_negative_jump_clipped_finite_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) :
    let first : Ω → WithTop ℝ≥0 := fun ω =>
      ⨅ u : ℝ≥0,
        if 0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
        then (u : WithTop ℝ≥0) else ⊤
    let stop : Ω → ℝ≥0 := fun ω =>
      (min (first ω) (T : WithTop ℝ≥0)).untopD T
    (∀ ω : Ω, stop ω ≤ T) ∧
      (∀ s : ℝ≥0,
        MeasurableSet[𝓕.rightCont s]
          {ω : Ω | stop ω ≤ s}) := by sorry
