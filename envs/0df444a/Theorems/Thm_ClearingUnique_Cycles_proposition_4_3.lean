-- Prove2me | Theorems.Thm_ClearingUnique_Cycles_proposition_4_3
-- name    : ClearingUnique.Cycles.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:53.097165+00:00
-- url     : https://prove2.me/theorems/8b2d5d32-bbc1-48cf-8423-944cf8169d73
-- title:
--   Proposition 4.3, p. 13 — payment differences propagate along a path
-- statement:
--   Let $P^-$ and $P^+$ be the least and greatest clearing matrices of a network $N$ satisfying the standing assumptions, and suppose $P^-_{i_1}<P^+_{i_1}$ in the strict row order. For a sequence $(i_1,\ldots,i_{k'})$, suppose that at each step $k<k'$ the rule of $i_k$ is positive monotonic, $e_{i_k}(P^+)=0$, and $P^+_{i_ki_{k+1}}>0$. Then
--
--   $$
--   P^-_{i_ki_{k+1}}<P^+_{i_ki_{k+1}}\qquad(1\le k<k').
--   $$
--
--   Thus a difference in outgoing payments persists along such a sequence of positive payment edges.
--
--   **Formalization Note** The sequence is indexed from $0$ in Lean, so its final index $K$ corresponds to $k'-1$ in the paper. The paper does not require its agents to be distinct.
-- source:
--   Csóka & Herings, Uniqueness of Clearing Payment Matrices in Financial Networks, GSBE Research Memorandum RM/21/014 (Maastricht University, 8 Sep 2021; doi:10.26481/umagsb.2021014), p. 13 (PDF 15), Proposition 4.3

import Mathlib
import Definitions.Def_ClearingUnique_Cycles_Model

namespace ClearingUnique.Cycles

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem proposition_4_3 (N : FinNetwork I) (hN : N.Standing)
    (Pm Pp : I → I → ℝ)
    (hm : IsLeast {P : I → I → ℝ | IsClearing N P} Pm)
    (hp : IsGreatest {P : I → I → ℝ | IsClearing N P} Pp)
    (s : ℕ → I) (K : ℕ)
    (hrow : RowLt Pm Pp (s 0))
    (hpath : ∀ k < K, PositiveMonotonic N (s k) ∧
      equity N Pp (s k) = 0 ∧ 0 < Pp (s k) (s (k + 1))) :
    ∀ k < K, Pm (s k) (s (k + 1)) < Pp (s k) (s (k + 1)) := by sorry

end ClearingUnique.Cycles
