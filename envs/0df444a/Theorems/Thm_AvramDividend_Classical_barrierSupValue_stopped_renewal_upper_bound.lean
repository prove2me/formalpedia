-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_bound
-- name    : AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T00:27:13.807839+00:00
-- url     : https://prove2.me/theorems/c6c3b1d0-2c2f-41ce-a5a0-2771efcc3a69
-- title:
--   Upper stopped-renewal bound for the reflected barrier reward
-- statement:
--   For a standing spectrally negative Levy model and a q-scale function W differentiable at a positive barrier a with nonzero derivative, the actual reflected barrier Stieltjes reward is eventually bounded above by the scale-function right finite-difference quotient ε W(a+ε)/(W(a+ε)−W(a)). This is the upper half of the exact hypothesis required by the Proved stopped-renewal derivative reduction.
-- source:
--   Source-faithful upper stochastic inequality required as hHi by AvramDividend.Classical.barrierSupValue_of_stopped_renewal_bounds (Proved, UUID 3c69ef7b-dc67-403c-b17c-ada181563a0a); the pathwise record-step estimate is AvramDividend.Classical.runningSup_stopped_two_firstRecord_steps_discount_bounds (Proved, UUID 1f8abe66-c253-4629-a2df-659435f2331c).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      barrierSupValue X a q ≤
        ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) := by sorry
