-- Prove2me | Theorems.Thm_ComplementFreeCA_CFRounding_eventB_bound
-- name    : ComplementFreeCA.CFRounding.eventB_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:18:19.683313+00:00
-- url     : https://prove2.me/theorems/909ab78d-9101-48e5-81ea-6a888e737d98
-- title:
--   §3.1.1 — Pr[B] < 3/4: the preallocation's welfare falls below OPT*/3 with probability < 3/4
-- statement:
--   Let $v_1,\dots,v_n$ be normalized, monotone valuations and let $x$ be LP-feasible with value $L=\sum_{i,S}x_{i,S}v_i(S)$. Suppose $L>3\,v_i(M)$ for every bidder $i$, i.e. $L>3\max_i v_i(M)$. Let $A=\sum_i v_i(S_i)$ be the welfare of the randomized-rounding preallocation and $B$ the event $A<L/3$. Then
--   $$\Pr[B]=\Pr\Big[A<\frac{L}{3}\Big]<\frac34.$$
--
--   Together with the items bound, this shows that one round of randomized rounding produces a preallocation with both required properties with constant probability.
--
--   **Formalization Note** The paper normalizes $\max_i v_i(M)=1$ and assumes $OPT^*>3$; the statement uses the scale-free equivalent $L>3\max_i v_i(M)$. The paper's definition of $B$ drops the sum ("$v_i(S_i)<\frac13 OPT^*$"); the display $\Pr[B]=\Pr[A<OPT^*/3]$ fixes the meaning used here. The paper's text announces $\Pr[B]<3/4$ and its display ends with $\le 3/4$; the strict inequality is stated, which the display's middle bound $9/(4\,OPT^*)$ with $OPT^*>3$ gives. The statement assumes only LP feasibility of $x$ (the paper uses the optimal $x$, which is a special case).
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 6, §3.1.1, the paragraph 'We will now prove that Pr[B] < 3/4' and the display bounding Pr[B]

import Mathlib
import Definitions.Def_ComplementFreeCA_CFRounding_Auction
import Definitions.Def_ComplementFreeCA_CFRounding_LP

namespace ComplementFreeCA.CFRounding

theorem eventB_bound {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (x : Fin n → Finset (Fin m) → ℝ) (hx : IsLPFeasible x)
    (hlarge : ∀ i, 3 * v i Finset.univ < lpValue v x) :
    roundProb x (fun σ => welfare v σ < lpValue v x / 3) < 3 / 4 := by sorry

end ComplementFreeCA.CFRounding
