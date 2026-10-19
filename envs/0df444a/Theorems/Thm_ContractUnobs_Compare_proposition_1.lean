-- Prove2me | Theorems.Thm_ContractUnobs_Compare_proposition_1
-- name    : ContractUnobs.Compare.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:56.608683+00:00
-- url     : https://prove2.me/theorems/54ffa7c3-29a0-4e14-b567-97aea8e50b70
-- title:
--   Proposition 1, p. 14 — unobservable two-part tariffs: contracts ((1+θ)/(2+θ)², 0), prices 1/(2+θ), Π = 2(1+θ)/(2+θ)², π_i = 0
-- statement:
--   Let $\theta \ge 0$ and consider the game in which the manufacturer offers each retailer a two-part tariff $(K, w)$, $w \ge 0$, that the other retailer does not observe, with passive beliefs. A passive-belief equilibrium exists, and in **every** such equilibrium, for both retailers $i$:
--
--   1. the contract is $$(K_i, w_i) = \Bigl(\frac{1+\theta}{(2+\theta)^2},\ 0\Bigr);$$
--   2. the retailer accepts and charges $p_i = \dfrac{1}{2+\theta}$;
--   3. the retailer's profit is $\pi_i = 0$;
--
--   and the manufacturer's profit is
--   $$\Pi = \frac{2(1+\theta)}{(2+\theta)^2}.$$
--
--   Under unobservability the manufacturer gives up the marginal wholesale price entirely and collects its profit through the fixed fees, which leaves the retailers nothing.
--
--   **Formalization Note** "In equilibrium" is read as a statement about every passive-belief equilibrium, together with existence. Order quantities are not pinned down: at $w = 0$ any order covering demand is optimal, and the page does not claim one.
-- source:
--   Li & Liu, Contract Unobservability and Downstream Competition, SSRN 3339702, p. 14, Proposition 1

import Mathlib
import Definitions.Def_ContractUnobs_Compare_Model

namespace ContractUnobs.Compare

theorem proposition_1 (θ : ℝ) (hθ : 0 ≤ θ) :
    (∃ E : Profile, IsPassiveEq θ tariffClass E) ∧
    ∀ E : Profile, IsPassiveEq θ tariffClass E →
      (∀ i : Fin 2, E.C i = ⟨(1 + θ) / (2 + θ) ^ 2, 0⟩ ∧ (E.onPath i).accept = true ∧
        (E.onPath i).p = 1 / (2 + θ) ∧ retProfit θ E i = 0) ∧
      mfrProfit E = 2 * (1 + θ) / (2 + θ) ^ 2 := by sorry

end ContractUnobs.Compare
