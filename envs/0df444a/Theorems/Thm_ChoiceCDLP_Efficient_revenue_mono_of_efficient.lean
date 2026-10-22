-- Prove2me | Theorems.Thm_ChoiceCDLP_Efficient_revenue_mono_of_efficient
-- name    : ChoiceCDLP.Efficient.revenue_mono_of_efficient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T07:27:17.842991+00:00
-- url     : https://prove2.me/theorems/c091f126-4cb1-4d31-8365-51b44ae76834
-- title:
--   Proposition 5 — for efficient S₁, S₂, Q(S₂) ≥ Q(S₁) implies R(S₂) ≥ R(S₁)
-- statement:
--   In the network choice model, let $S_1$ and $S_2$ be two efficient offer sets. If $Q(S_2) \ge Q(S_1)$ componentwise, then
--   $$R(S_2) \ge R(S_1).$$
--
--   Efficient sets are therefore partially ordered: an efficient set that consumes at least as much capacity on every leg earns at least as much expected revenue. In the single-leg model this ordering is total; in the network model it is only partial.
--
--   **Formalization Note.** $Q(S_2) \ge Q(S_1)$ is the componentwise (Pi) order on $\mathbb{R}^m$.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 297, Proposition 5

import Mathlib
import Definitions.Def_ChoiceCDLP_Efficient_ChoiceNetwork
import Definitions.Def_ChoiceCDLP_Efficient_IsEfficient

namespace ChoiceCDLP.Efficient

/-- Proposition 5 (p. 297): if `S₁` and `S₂` are efficient sets and `Q(S₂) ≥ Q(S₁)`
componentwise, then `R(S₂) ≥ R(S₁)`. -/
theorem revenue_mono_of_efficient {m n : ℕ} (N : ChoiceNetwork m n)
    (S₁ S₂ : Finset (Fin n)) (h₁ : IsEfficient N S₁) (h₂ : IsEfficient N S₂)
    (hQ : consumption N S₁ ≤ consumption N S₂) :
    revenue N S₁ ≤ revenue N S₂ := by sorry

end ChoiceCDLP.Efficient
