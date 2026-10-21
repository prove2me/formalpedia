-- Prove2me | Theorems.Thm_ContractUnobs_Compare_proposition_2
-- name    : ContractUnobs.Compare.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:05.662748+00:00
-- url     : https://prove2.me/theorems/70cdd1f1-28c9-4a5e-8cb7-fe1c3aa4c6bd
-- title:
--   Proposition 2, p. 16 — unobservable wholesale prices: w_i = 2/(4+θ), p_i = 3/(4+θ), Π = 4(1+θ)/(4+θ)², π_i = (1+θ)/(4+θ)²
-- statement:
--   Let $\theta \ge 0$ and consider the game in which the manufacturer offers each retailer a wholesale price $w \ge 0$ (no fixed fee) that the other retailer does not observe, with passive beliefs. A passive-belief equilibrium exists, and in **every** such equilibrium, for both retailers $i$:
--
--   1. the wholesale price is $$w_i = \frac{2}{4+\theta};$$
--   2. the retailer accepts and charges $p_i = \dfrac{3}{4+\theta}$;
--   3. the retailer's profit is $$\pi_i = \frac{1+\theta}{(4+\theta)^2};$$
--
--   and the manufacturer's profit is
--   $$\Pi = \frac{4(1+\theta)}{(4+\theta)^2}.$$
--
--   Compared with the observable case, unobservability pushes the wholesale price down, which intensifies retail competition.
--
--   **Formalization Note** "In equilibrium" is read as a statement about every passive-belief equilibrium, together with existence. Contracts are written as pairs $(K, w)$ with $K = 0$.
-- source:
--   Li & Liu, Contract Unobservability and Downstream Competition, SSRN 3339702, p. 16, Proposition 2

import Mathlib
import Definitions.Def_ContractUnobs_Compare_Model

namespace ContractUnobs.Compare

theorem proposition_2 (θ : ℝ) (hθ : 0 ≤ θ) :
    (∃ E : Profile, IsPassiveEq θ wholesaleClass E) ∧
    ∀ E : Profile, IsPassiveEq θ wholesaleClass E →
      (∀ i : Fin 2, E.C i = ⟨0, 2 / (4 + θ)⟩ ∧ (E.onPath i).accept = true ∧
        (E.onPath i).p = 3 / (4 + θ) ∧ retProfit θ E i = (1 + θ) / (4 + θ) ^ 2) ∧
      mfrProfit E = 4 * (1 + θ) / (4 + θ) ^ 2 := by sorry

end ContractUnobs.Compare
