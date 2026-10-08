-- Prove2me | Theorems.Thm_CachonCoord_Proportional_coordinating_buyback
-- name    : CachonCoord.Proportional.coordinating_buyback
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:44:52.562671+00:00
-- url     : https://prove2.me/theorems/7612c570-2766-4a6d-9047-04a2df60afab
-- title:
--   §6.5.1, pp. 51–53 — with w = w_b(b), every retailer ordering q°/n is the unique Nash equilibrium; retailers earn ((p − b)/(pn²))Π(q°), the supplier ((p(n − 1) + b)/(pn))Π(q°)
-- statement:
--   Consider $n \ge 2$ competing retailers with proportional allocation of total demand, a buy-back rate $b < p$, the integrated optimum $q^o$ solving (20), $F(q^o) = (p-c)/p$, and the wholesale price
--
--   $$
--   w_b(b) = p - (p-b)\left[\frac1n\left(\frac{p-c}{p}\right) + \left(\frac{n-1}{n}\right)\left(\frac1{q^o}\int_0^{q^o}F(x)\,dx\right)\right].
--   $$
--
--   Then:
--
--   1. $q^o$ maximizes the chain's profit $\Pi(q) = pS(q) - cq$ over $q \ge 0$;
--   2. $b < w_b(b) < p$;
--   3. under the contract $(w_b(b), b)$ the profile in which every retailer orders $q^o/n$ is the **unique** Nash equilibrium, so the contract coordinates the supply chain;
--   4. at that equilibrium each retailer earns
--   $$\pi_i(q^*_i, q^*_{-i}) = \left(\frac{p-b}{pn^2}\right)\Pi(q^o);$$
--   5. the supplier, who receives $w_b(b)$ per unit, pays $c$ per unit produced and $b$ per unit returned, earns
--   $$\pi_s(q^o, w_b(b), b) = \left(\frac{p(n-1)+b}{pn}\right)\Pi(q^o).$$
--
--   The family $\{(w_b(b), b)\}$ thus coordinates the chain while letting the supplier's share range from $(n-1)/n$ (at $b = 0$) towards all of $\Pi(q^o)$ (as $b \to p$).
--
--   **Formalization Note** The supplier's profit is computed from the transfers $w_b(b)q^o - cq^o - b\,\mathbb E[(q^o - D)^+]$, not as $\Pi(q^o)$ minus the retailers' profits; the page derives it the second way. The page's "$w(b)$" in the retailer-profit display is $w_b(b)$. $b < p$ keeps $(p - w)/(p - b)$ defined; the page's endpoint $b = p$ is a separate companion item. The hypotheses on the demand law are the chapter's standing assumptions (p. 7), carried by the model.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.1, pp. 51–53 (unique equilibrium p. 51; w_b(b) p. 52; retailer and supplier profits p. 53)

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- §6.5.1, pp. 51–53, the coordinating buy-back contract. Let `n ≥ 2`, `b < p`, and let `q°`
solve (20), `F(q°) = (p − c)/p`; let `w = w_b(b)` (p. 52). Then `q°` maximizes the chain profit,
`b < w < p`, the profile in which every retailer orders `q°/n` is the unique Nash equilibrium,
each retailer earns `((p − b)/(pn²)) Π(q°)` there, and the supplier, who receives `w q°`, pays
`c q°` in production and `b` per unit returned, earns `((p(n − 1) + b)/(pn)) Π(q°)`. -/
theorem coordinating_buyback (M : Model) (n : ℕ) (hn : 2 ≤ n) (b qo : ℝ) (hb : b < M.p)
    (hqo : M.F qo = (M.p - M.c) / M.p) :
    IsMaxOn M.chainProfit (Set.Ici 0) qo ∧
      b < M.wb n b qo ∧ M.wb n b qo < M.p ∧
      (∀ q : Fin n → ℝ, M.IsNashEq (M.wb n b qo) b q ↔ ∀ i, q i = qo / n) ∧
      (∀ i : Fin n, M.payoff (M.wb n b qo) b i (fun _ => qo / n) =
        (M.p - b) / (M.p * (n : ℝ) ^ 2) * M.chainProfit qo) ∧
      M.supplierProfit (M.wb n b qo) b qo =
        (M.p * ((n : ℝ) - 1) + b) / (M.p * n) * M.chainProfit qo := by sorry

end CachonCoord.Proportional
