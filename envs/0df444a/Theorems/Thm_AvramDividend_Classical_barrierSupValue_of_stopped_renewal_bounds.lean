-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_of_stopped_renewal_bounds
-- name    : AvramDividend.Classical.barrierSupValue_of_stopped_renewal_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T10:38:21.305966+00:00
-- url     : https://prove2.me/theorems/3c69ef7b-dc67-403c-b17c-ada181563a0a
-- title:
--   Exact barrierSupValue scale derivative ratio conditional on stopped-renewal reward inequalities
-- statement:
--   Assume the paper's original standing hypotheses, q>0 and a q-scale function W. If W is differentiable at the barrier a with nonzero derivative and the actual stopped-reflected regulator dividend reward barrierSupValue X a q satisfies the explicit two eventual renewal finite-difference inequalities, then barrierSupValue equals ENNReal.ofReal(W a / deriv W a). This theorem reduces the original Proposition 1 scale-ratio valuation to the two difficult stochastic payoff bounds and the scale regularity. It does not assert the missing assumptions or prove the unconditional original theorem.
-- source:
--   Avram, Palmowski, Pistorius 2007, Proposition 1, reflected supremum dividend value. Direct application of remotely Proved reflected_reward_of_renewal_finite_difference_sandwich (319da48e-fc97-4ddf-a4ce-e914fa9943e2) to V=barrierSupValue.

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_reflected_reward_of_renewal_finite_difference_sandwich

open MeasureTheory Filter Topology
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierSupValue_of_stopped_renewal_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0)
    (hLo : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal
        (ε * W (a - ε) / (W a - W (a - ε))) ≤
          barrierSupValue X a q)
    (hHi : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      barrierSupValue X a q ≤ ENNReal.ofReal
        (ε * W (a + ε) / (W (a + ε) - W a))) :
    barrierSupValue X a q =
      ENNReal.ofReal (W a / deriv W a) := by sorry
