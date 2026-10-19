-- Prove2me | Theorems.Thm_ContractUnobs_Compare_proposition_3
-- name    : ContractUnobs.Compare.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:55.824414+00:00
-- url     : https://prove2.me/theorems/185b1a25-5ea9-4cd4-b192-eef19d5083e9
-- title:
--   Proposition 3, p. 18 — under unobservable contracts, wholesale prices beat two-part tariffs for the manufacturer iff θ ≥ 2√2, for the retailers always, for the industry iff θ ≥ √3 − 1
-- statement:
--   Let $\theta \ge 0$. Consider the two games with unobservable contracts and passive beliefs: one in which the manufacturer offers two-part tariffs $(K,w)$, $w \ge 0$, and one in which it offers wholesale prices $w \ge 0$. Both games have a passive-belief equilibrium, and for **every** equilibrium $E^T$ of the tariff game and **every** equilibrium $E^W$ of the wholesale-price game:
--
--   1. the manufacturer's profit is at least as high under wholesale prices exactly when $\theta \ge 2\sqrt2$, and strictly higher exactly when $\theta > 2\sqrt2$:
--   $$\Pi(E^T) \le \Pi(E^W) \iff \theta \ge 2\sqrt2, \qquad \Pi(E^T) < \Pi(E^W) \iff \theta > 2\sqrt2;$$
--   2. each retailer's profit is strictly higher under wholesale prices: $\pi_i(E^T) < \pi_i(E^W)$ for $i = 1, 2$;
--   3. the total industry profit (manufacturer plus both retailers) is at least as high under wholesale prices exactly when $\theta \ge \sqrt3 - 1$, and strictly higher exactly when $\theta > \sqrt3 - 1$:
--   $$\Pi_{\mathrm{ind}}(E^T) \le \Pi_{\mathrm{ind}}(E^W) \iff \theta \ge \sqrt3 - 1, \qquad \Pi_{\mathrm{ind}}(E^T) < \Pi_{\mathrm{ind}}(E^W) \iff \theta > \sqrt3 - 1.$$
--
--   Under observable contracts the manufacturer always prefers two-part tariffs. Unobservability reverses this when retail competition is intense: the wholesale price then serves as a commitment to soften competition, and both the manufacturer and the retailers gain.
--
--   **Formalization Note** The page says "higher … when $\theta \ge 2\sqrt2$" (resp. $\sqrt3 - 1$). At the threshold the two profits are equal, so the statement is formalized as an equivalence for "at least as high" together with one for "strictly higher". The converse direction (wholesale prices are worse below the threshold) is a disclosed strengthening, shown on the page's Figures 3 and 5; without it the threshold would not be determined. "The retailer's profits" is read per retailer. The existence conjuncts exclude a vacuous reading. The comparison is about equilibrium profiles of the two games, not about the closed-form values of Propositions 1–2.
-- source:
--   Li & Liu, Contract Unobservability and Downstream Competition, SSRN 3339702, p. 18, Proposition 3

import Mathlib
import Definitions.Def_ContractUnobs_Compare_Model

namespace ContractUnobs.Compare

theorem proposition_3 (θ : ℝ) (hθ : 0 ≤ θ) :
    (∃ ET : Profile, IsPassiveEq θ tariffClass ET) ∧
    (∃ EW : Profile, IsPassiveEq θ wholesaleClass EW) ∧
    ∀ ET EW : Profile, IsPassiveEq θ tariffClass ET → IsPassiveEq θ wholesaleClass EW →
      ((mfrProfit ET ≤ mfrProfit EW ↔ 2 * Real.sqrt 2 ≤ θ) ∧
        (mfrProfit ET < mfrProfit EW ↔ 2 * Real.sqrt 2 < θ)) ∧
      (∀ i : Fin 2, retProfit θ ET i < retProfit θ EW i) ∧
      ((industryProfit θ ET ≤ industryProfit θ EW ↔ Real.sqrt 3 - 1 ≤ θ) ∧
        (industryProfit θ ET < industryProfit θ EW ↔ Real.sqrt 3 - 1 < θ)) := by sorry

end ContractUnobs.Compare
