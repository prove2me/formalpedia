-- Prove2me | Theorems.Thm_BudgetMgmt_Profit_expend_sym
-- name    : BudgetMgmt.Profit.expend_sym
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-29T21:06:25.688867+00:00
-- url     : https://prove2.me/theorems/d85860dc-1cac-4bef-a93b-e8ab33486f15
-- title:
--   Symmetric setting, p. 21 — at a symmetric profile every buyer spends $G_i(s_1\vec 1)=G_1(s_1)$
-- statement:
--   Consider a symmetric correlated instance: $n$ buyers whose values $x=(x_1,\dots,x_n)$ have an exchangeable joint density $f$ (that is, $f(x\circ\sigma)=f(x)$ for every permutation $\sigma$ of the buyers), $T$ items and opportunity cost $c>0$. Let $m$ be one of the budget management mechanisms of Table 1 — thresholding, reserve pricing or bid shading — and let every buyer use the same parameter $s_1\in\mathbb R$ (the symmetric profile $s_1\vec 1$). Write $G_i(s)=T\,\mathbb E[M_i(x;s)]$ for buyer $i$'s expected expenditure and $G_1(s_1)=G_1(s_1\vec1)$ for that of the reference buyer. Then for every buyer $i$,
--
--   $$G_i(s_1\vec 1)=G_1(s_1).$$
--
--   This is the symmetry used throughout Section 4 (p. 21) to reduce a symmetric equilibrium to a one-variable problem; in particular the seller's profit at a symmetric profile is $P(s_1\vec1)=\sum_iG_i(s_1\vec1)-c\,I(s_1\vec1)=n\,G_1(s_1)-c\,I(s_1\vec1)$, the form used in the proof of Theorem 4.2 (pp. ec 44–47).
--
--   **Formalization Note** Ties between buyers are broken in favour of the lowest index; since the values have a density, ties have probability zero, so the identity holds for every buyer index $i$ and every real $s_1$.
-- source:
--   Balseiro, Kim, Mahdian & Mirrokni, Budget management strategies in repeated auctions, SSRN 2858261 (version of July 8, 2020), p. 21 (symmetric setting, $G_1(s_1)$; used for $P=nG_1-cI$ in the proof of Theorem 4.2, pp. ec 44–47)

import Mathlib
import Definitions.Def_BudgetMgmt_Profit_Model

namespace BudgetMgmt.Profit

/-- Symmetric setting, p. 21: at a symmetric parameter profile `s₁ 1⃗`, every buyer's expected
expenditure equals the reference buyer's, `G_i(s₁ 1⃗) = G₁(s₁)`, for thresholding, reserve pricing
and bid shading. -/
theorem expend_sym {n : ℕ} [NeZero n] (P : SymInstance n) (m : Mech) (s₁ : ℝ) (i : Fin n) :
    expend P m (sym s₁) i = G1 P m s₁ := by sorry

end BudgetMgmt.Profit
