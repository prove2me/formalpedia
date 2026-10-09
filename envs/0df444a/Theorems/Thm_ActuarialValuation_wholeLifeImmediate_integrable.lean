-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeImmediate_integrable
-- name    : ActuarialValuation.wholeLifeImmediate_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:30:48.151035+00:00
-- url     : https://prove2.me/theorems/01ed3421-746b-4344-92ce-a80be0f5eba3
-- title:
--   Whole-life immediate PV is integrable under discounted survival
-- statement:
--   If the discount factor satisfies 0 ≤ v < 1, the whole-life immediate present value is bounded by a convergent geometric series and is integrable under any curtate-lifetime distribution. This supplies an analytic justification for expected-value results, rather than a separate textbook numbered formula.
--
--   **Mathematical statement**
--
--   $$
--   0\le v<1\Longrightarrow Z_{\mathrm{WL,immediate}}\in L^1(P)
--   $$
-- source:
--   Analytic justification for expected values in Chapter 3 §3.3.1 and §3.3.3; equations (3.3), (3.11), (3.12), (3.17), (3.18), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityImmediatePV
open MeasureTheory

namespace ActuarialValuation

theorem wholeLifeImmediate_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1)
    :
    Integrable (wholeLifeAnnuityImmediatePV K v) P := by sorry

end ActuarialValuation
