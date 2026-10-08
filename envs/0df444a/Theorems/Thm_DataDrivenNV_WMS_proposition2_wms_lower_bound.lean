-- Prove2me | Theorems.Thm_DataDrivenNV_WMS_proposition2_wms_lower_bound
-- name    : DataDrivenNV.WMS.proposition2_wms_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:36:27.386713+00:00
-- url     : https://prove2.me/theorems/0f16aa5d-9f82-4751-b838-0e88b8527b25
-- title:
--   Proposition 2, p. 15 — every log-concave demand has weighted mean spread Δ(q*)f(q*) ≥ min(b,h)/(b+h)
-- statement:
--   Let $b>0$ be the unit underage cost and $h>0$ the unit overage cost of a newsvendor. Let the demand $D$ have a log-concave probability density $f$ with cdf $F$, let $q^*=\inf\{q:F(q)\ge b/(b+h)\}$ be its $b/(b+h)$ quantile, and let
--   $$\Delta(q^*)=E(D\mid D\ge q^*)-E(D\mid D\le q^*)$$
--   be its absolute mean spread. Then the weighted mean spread satisfies
--   $$\Delta(q^*)\,f(q^*)\ \ge\ \frac{\min(b,h)}{b+h}.$$
--
--   The weighted mean spread governs the probability that the (biased) sample-average-approximation order quantity is $\epsilon$-optimal (Theorem 3 of the paper); this proposition makes that guarantee uniform over all log-concave demand distributions, independently of their parameters.
--
--   **Formalization Note** Log-concavity is the published `LogConcaveOn Set.univ f` in the power form, which admits densities vanishing outside an interval (uniform, exponential). No integrability of $x f(x)$ is assumed: a log-concave density has exponential tails, so both conditional means exist. The value $f(q^*)$ is meaningful pointwise: since $0<F(q^*)<1$, $q^*$ lies in the interior of the interval $\{f>0\}$, where a log-concave $f$ is continuous and determined by its law. The case $\gamma_1=0$ and the boundary cases of the paper's proof are covered by the statement, which has no restriction.
-- source:
--   Levi, Perakis & Uichanco, The Data-Driven Newsvendor Problem: New Bounds and Insights, authors' accepted manuscript (MIT DSpace), p. 15, Proposition 2; proof p. 16

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_DataDrivenNV_WMS_Setting

namespace DataDrivenNV.WMS

open MeasureTheory

/-- **Proposition 2** (p. 15): if `D` has a log-concave pdf `f` with `b/(b+h)` quantile `q*`
and AMS `Δ(q*)`, then the weighted mean spread satisfies `Δ(q*) f(q*) ≥ min(b,h)/(b+h)`. -/
theorem proposition2_wms_lower_bound (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    (f : ℝ → ℝ) (hf : IsPdf f) (hlc : ConvexOptimization.LogConcaveOn Set.univ f) :
    min b h / (b + h) ≤
      ams f (quantileOf f (b / (b + h))) * f (quantileOf f (b / (b + h))) := by sorry

end DataDrivenNV.WMS
