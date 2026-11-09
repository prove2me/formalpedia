-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_display_2
-- name    : BulowKlemperer429.Bundling.display_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:58.849753+00:00
-- url     : https://prove2.me/theorems/f26d6cb3-3b98-4680-b693-b7bc92f88410
-- title:
--   Display (2) — derivative bound for the regular quantile
-- statement:
--   Let $X$ have a nonnegative probability law $F$ with concave revenue curve, and let $v=v_F$ be its upper-tail quantile. For Lebesgue-almost every $q\in(0,1)$, $v$ is differentiable and
--   $$q(1-q)(-v'(q))\le v(q).$$
--   This is the quantile inequality displayed as (2), used in the regular scalar comparison. Differentiability and the almost-everywhere domain make the derivative notation precise.
--
--   Differences from the source:
--   - encoding: finite monopoly revenue assumed throughout → no separate finite-revenue hypothesis for regular marginals; reason: the nonnegative concave revenue curve is bounded on (0,1), which implies finite posted-price revenue
--   - encoding: the derivative inequality holds almost everywhere on (0,1) → a.e. with respect to Lebesgue measure restricted to Ioo 0 1, with differentiability explicitly conjoined; reason: the preceding source sentence supplies the almost-everywhere qualifier and the derivative notation presupposes existence there
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 8, Display (2) and the preceding sentence (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_Revenue
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling

theorem display_2 (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (hreg : IsRegular ν) :
    ∀ᵐ q : ℝ ∂(volume.restrict (Set.Ioo 0 1)),
      DifferentiableAt ℝ (tailQuantile ν) q ∧
      q * (1 - q) * (-deriv (tailQuantile ν) q) ≤ tailQuantile ν q := by sorry

end BulowKlemperer429.Bundling
