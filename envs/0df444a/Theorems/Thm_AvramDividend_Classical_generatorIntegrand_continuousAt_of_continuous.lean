-- Prove2me | Theorems.Thm_AvramDividend_Classical_generatorIntegrand_continuousAt_of_continuous
-- name    : AvramDividend.Classical.generatorIntegrand_continuousAt_of_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:20:18.659673+00:00
-- url     : https://prove2.me/theorems/93c5e7b5-6f3a-4ac7-94a3-12c2e37a285a
-- title:
--   Continuity of a compensated Lévy generator increment at a fixed jump
-- statement:
--   For any function W and fixed jump y, if W is continuous at x and at x+y and W' is continuous at x, then z↦W(z+y)-W(z)-W'(z)y*1_{(-1,1)}(y) is continuous at x. This identifies the sole potential discontinuity in the compensated jump term: the shifted argument x+y reaching the scale-function origin, relevant for BV Lévy processes with W(0)>0.
-- source:
--   Continuous-function algebra applied to the actual SpectrallyNegativeLevy.generatorIntegrand definition in the Avram Dividend mission.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generatorIntegrand_continuousAt_of_continuous
    (W : ℝ → ℝ) (x y : ℝ)
    (hWx : ContinuousAt W x)
    (hWxy : ContinuousAt W (x + y))
    (hderiv : ContinuousAt (deriv W) x) :
    ContinuousAt
      (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand W z y) x := by sorry

end AvramDividend.Classical
