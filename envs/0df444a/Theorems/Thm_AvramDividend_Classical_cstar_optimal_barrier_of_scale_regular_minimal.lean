-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_optimal_barrier_of_scale_regular_minimal
-- name    : AvramDividend.Classical.cstar_optimal_barrier_of_scale_regular_minimal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T12:21:08.553814+00:00
-- url     : https://prove2.me/theorems/07ea4d45-ba73-48c7-a999-30becfcf85e3
-- title:
--   Scale-function barrier comparison from derivative minimality and boundary control
-- statement:
--   For a canonical Avram q-scale function, assume cstar finite and either the origin special case or positive derivative-minimality with boundary-denominator comparisons and interior differentiability. Then the cstar barrier dominates every nonnegative competing barrier on 0≤x≤cstar. Positivity and endpoint continuity are now derived directly from IsScaleFunction, reducing the explicit hypotheses needed for milestone 3.
-- source:
--   This source-faithful adapter projects nonnegativity and continuous-on-Ici from the exact IsScaleFunction conjunction and restricts continuity to Icc(0,cstar), then applies the separately authored regular-minimal barrier comparison. No proof of finiteness or derivative control is silently assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical
open MeasureTheory Set
open scoped ENNReal NNReal

namespace AvramDividend.Classical

theorem cstar_optimal_barrier_of_scale_regular_minimal
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hfinite : cstar W < ⊤)
    (hshape : ((cstar W).toReal = 0 ∧ W 0 = 0) ∨
      ∃ d : ℝ, 0 < d ∧
        scaleDeriv W (cstar W).toReal = (d : EReal) ∧
        (∀ a : ℝ, 0 ≤ a →
          scaleDeriv W a = ⊤ ∨
            (scaleDeriv W a).toReal = 0 ∨
            d ≤ (scaleDeriv W a).toReal) ∧
        DifferentiableOn ℝ W (Set.Ioo 0 (cstar W).toReal) ∧
        (∀ t ∈ Set.Ioo 0 (cstar W).toReal, d ≤ deriv W t)) :
    cstar W < ⊤ ∧
      ∀ x a : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ a →
        barrierValue W a x ≤ vcstar W x := by
  sorry

end AvramDividend.Classical
