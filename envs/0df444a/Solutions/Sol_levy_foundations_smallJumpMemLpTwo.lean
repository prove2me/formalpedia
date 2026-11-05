-- Prove2me | solution 1 for levy_foundations_smallJumpMemLpTwo
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:38:26.501974+00:00
-- url     : https://prove2.me/submissions/5505e8f2-9b3f-4904-863c-1d5084b5c7c8

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_levy_foundations_isLevyMeasure
import Theorems.Thm_levy_foundations_smallJumpBandMemLpTwo

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution
    (ν : Measure ℝ) [SigmaFinite ν]
    (hν : LevyFoundations.isLevyMeasure ν) (t : ℝ) :
    MemLp ((Set.Ioc 0 t ×ˢ Set.Ioo (-1) 1).indicator
      (fun p : ℝ × ℝ => p.2)) 2 (volume.prod ν) := by
  exact levy_foundations_smallJumpBandMemLpTwo ν hν 0 t
