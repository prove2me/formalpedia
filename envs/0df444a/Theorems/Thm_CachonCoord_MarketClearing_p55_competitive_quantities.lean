-- Prove2me | Theorems.Thm_CachonCoord_MarketClearing_p55_competitive_quantities
-- name    : CachonCoord.MarketClearing.p55_competitive_quantities
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:42:55.835576+00:00
-- url     : https://prove2.me/theorems/b60e729b-fe76-4fcb-8f1e-b12492e32878
-- title:
--   §6.5.2, p. 55 — the competitive order is q₁(w) = (2θ/(1 + θ))(1 − w) or q₂(w) = θ(1 − 2w)
-- statement:
--   Let $\theta>1$ and let $0\le w<1$ be the wholesale price. Write $\bar w_0=\tfrac12-\tfrac1{2\theta}$, $q_1(w)=\frac{2\theta}{1+\theta}(1-w)$ and $q_2(w)=\theta(1-2w)$. Then
--   1. $q_1(w)\le1$ if and only if $w\ge\bar w_0$, and $q_2(w)>1$ if and only if $w<\bar w_0$;
--   2. if $w\ge\bar w_0$, the perfectly competitive total order (the first $q>0$ at which the retailers' expected profit $\tfrac12p_l(q)q+\tfrac12p_h(q)q-wq$ vanishes, the profit being positive below it) exists and equals $q_1(w)$;
--   3. if $w<\bar w_0$, it exists and equals $q_2(w)$.
--
--   This identifies the equilibrium order on which the supplier's choice of wholesale price is based.
--
--   **Formalization Note** The range $0\le w<1$ is where a positive competitive order exists; the page leaves it implicit.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.2, p. 55, displays q₁(w) and q₂(w) and the two conditions following them

import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model

namespace CachonCoord.MarketClearing

/-- §6.5.2, p. 55: `q₁(w) ≤ 1` iff `w ≥ (1/2) − 1/(2θ)`, `q₂(w) > 1` iff `w < (1/2) − 1/(2θ)`, and for
a wholesale price `0 ≤ w < 1` the perfectly competitive total order is `q₁(w)` in the first case and
`q₂(w)` in the second (it exists and is unique). -/
theorem p55_competitive_quantities (θ w : ℝ) (hθ : 1 < θ) (hw0 : 0 ≤ w) (hw1 : w < 1) :
    (q1 θ w ≤ 1 ↔ wBar0 θ ≤ w) ∧
    (1 < q2 θ w ↔ w < wBar0 θ) ∧
    (wBar0 θ ≤ w → ∀ q : ℝ, IsCompetitiveOrder (retailerProfit θ w) q ↔ q = q1 θ w) ∧
    (w < wBar0 θ → ∀ q : ℝ, IsCompetitiveOrder (retailerProfit θ w) q ↔ q = q2 θ w) := by sorry

end CachonCoord.MarketClearing
