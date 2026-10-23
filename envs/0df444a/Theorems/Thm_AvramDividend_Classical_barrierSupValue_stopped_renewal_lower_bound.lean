-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_lower_bound
-- name    : AvramDividend.Classical.barrierSupValue_stopped_renewal_lower_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-23T00:27:15.393885+00:00
-- url     : https://prove2.me/theorems/6b821aa5-c792-4436-8eca-fc9429115ef9
-- title:
--   Lower stopped-renewal bound for the reflected barrier reward
-- statement:
--   For a standing spectrally negative Levy model and a q-scale function W differentiable at a positive barrier a with nonzero derivative, the actual reflected barrier Stieltjes reward is eventually bounded below by the scale-function left finite-difference quotient ε W(a−ε)/(W(a)−W(a−ε)). This is the lower half of the exact hypothesis required by the Proved stopped-renewal derivative reduction.
-- source:
--   Source-faithful lower stochastic inequality required as hLo by AvramDividend.Classical.barrierSupValue_of_stopped_renewal_bounds (Proved, UUID 3c69ef7b-dc67-403c-b17c-ada181563a0a); the pathwise record-step estimate is AvramDividend.Classical.runningSup_stopped_two_firstRecord_steps_discount_bounds (Proved, UUID 1f8abe66-c253-4629-a2df-659435f2331c).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierSupValue_stopped_renewal_lower_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε * W (a - ε) / (W a - W (a - ε))) ≤
        barrierSupValue X a q := by sorry
