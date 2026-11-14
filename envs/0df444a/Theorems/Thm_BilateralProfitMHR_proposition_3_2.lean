-- Prove2me | Theorems.Thm_BilateralProfitMHR_proposition_3_2
-- name    : BilateralProfitMHR.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:34.622126+00:00
-- url     : https://prove2.me/theorems/d63310a7-1bf3-4958-bcc2-20a2c3522478
-- title:
--   Proposition 3.2 — under MHR, $L=-\log\mu$ is continuous and convex on the interior of $\mathcal T$
-- statement:
--   Let the seller and buyer values be independent with densities strictly positive on $[0,1]$, and let both satisfy the monotone hazard rate property (Definition 2.3). Let $\mu(p,q)=(q-p)P(p,q)$ be the expected profit, where $P(p,q)=\Pr(s\le p,\ b\ge q)$. Then the loss
--   $$L(p,q)=-\log\mu(p,q)$$
--   is continuous and convex on the interior $\{(p,q):0<p<q<1\}$ of the triangle $\mathcal T$.
--
--   Convexity of $L$ is what turns profit maximization into a stochastic convex optimization problem, to which Corollary 3.1 applies.
--
--   Differences from the source:
--   - encoding: "under the MHR assumption" (with §2's standing independent laws with strictly positive densities on $[0,1]$) → an environment with supports $[0,1]$ satisfying MHR for both agents; reason: this is §2's class exactly; the reused environment adds no condition
--   - encoding: "the interior of $\mathcal T$" → the set $\{0<p<q<1\}$; reason: this set is the interior of $\mathcal T$ in $\mathbb R^2$, and $\mu>0$ on it, so the logarithm is the true one
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Proposition 3.2, p.11 (PDF 13); restated with proof p.30 (PDF 32)

import Mathlib
import Definitions.Def_BilateralProfitMHR_Model

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade

/-- **Proposition 3.2**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…),
p.11 (PDF 13), restated with proof p.30 (PDF 32): under the MHR assumption, the loss function
`L(p, q) = −log µ(p, q)` is continuous and convex in the interior of `𝒯`.

Stated for every environment with independent seller and buyer values whose densities are
strictly positive on `[0, 1]` and both MHR (Definition 2.3), with `µ` the expected profit under
the product law `E.prior`.

**Formalization Note.** The interior of `𝒯 = {(p, q) ∈ [0,1]² : p ≤ q}` in `ℝ²` is
`intT = {0 < p < q < 1}`. On it `µ > 0` (positive densities), so `Real.log` is the true
logarithm there; no smoothness of the densities is assumed. -/
theorem proposition_3_2 (E : Environment) (hE : UnitSupport E) (hM : IsMHR E) :
    ContinuousOn (lossL E.prior) intT ∧ ConvexOn ℝ intT (lossL E.prior) := by sorry

end BilateralProfitMHR
