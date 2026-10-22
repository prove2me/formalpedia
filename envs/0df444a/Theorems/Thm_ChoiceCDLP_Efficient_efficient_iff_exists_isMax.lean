-- Prove2me | Theorems.Thm_ChoiceCDLP_Efficient_efficient_iff_exists_isMax
-- name    : ChoiceCDLP.Efficient.efficient_iff_exists_isMax
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T07:27:07.422744+00:00
-- url     : https://prove2.me/theorems/0ffb90b7-f412-4646-b219-f20dd73a5d58
-- title:
--   Proposition 3 — T is efficient iff T maximizes R(S) − πᵀQ(S) for some π ≥ 0
-- statement:
--   In the network choice model, an offer set $T$ is efficient if and only if there is a vector of leg prices $\pi = (\pi_1, \dots, \pi_m)^\top \ge 0$ such that $T$ is an optimal solution of
--   $$\max_{S \subseteq N} \big\{ R(S) - \pi^\top Q(S) \big\},$$
--   that is, $R(S) - \pi^\top Q(S) \le R(T) - \pi^\top Q(T)$ for every offer set $S$.
--
--   In words: the efficient sets are exactly the offer sets that maximize revenue net of capacity charged at some nonnegative leg prices. Letting $\pi$ range over all nonnegative vectors and collecting the maximizers generates all efficient sets. The "if" direction is the step used in the proof of Proposition 4.
--
--   **Formalization Note.** The paper writes "$T$ is *the* optimal solution"; the statement is formalized as "$T$ is *an* optimal solution" (a maximizer, not necessarily unique). Read as a unique maximizer, the "only if" direction would be false: two offer sets with equal $R$ and equal $Q$ (for example, $T'$ obtained from $T$ by adding a product $j$ with $P_j(T') = 0$ and all other probabilities unchanged) are both efficient, and neither is the unique maximizer for any $\pi$. $\pi^\top Q(S)$ is the dot product `dotProduct π (consumption N S)`; $\pi \ge 0$ is componentwise.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 296, Proposition 3 (proof: Appendix, pp. 307 and 309)

import Mathlib
import Definitions.Def_ChoiceCDLP_Efficient_ChoiceNetwork
import Definitions.Def_ChoiceCDLP_Efficient_IsEfficient

namespace ChoiceCDLP.Efficient

/-- Proposition 3 (p. 296): an offer set `T` is efficient if and only if, for some `π ≥ 0`, `T`
is an optimal solution of `max_S {R(S) − πᵀ Q(S)}` (7). -/
theorem efficient_iff_exists_isMax {m n : ℕ} (N : ChoiceNetwork m n) (T : Finset (Fin n)) :
    IsEfficient N T ↔
      ∃ π : Fin m → ℝ, 0 ≤ π ∧
        ∀ S : Finset (Fin n),
          revenue N S - dotProduct π (consumption N S) ≤
            revenue N T - dotProduct π (consumption N T) := by sorry

end ChoiceCDLP.Efficient
