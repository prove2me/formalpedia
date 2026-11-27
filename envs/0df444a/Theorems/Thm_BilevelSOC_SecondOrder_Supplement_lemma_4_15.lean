-- Prove2me | Theorems.Thm_BilevelSOC_SecondOrder_Supplement_lemma_4_15
-- name    : BilevelSOC.SecondOrder.Supplement.lemma_4_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T07:51:37.174684+00:00
-- url     : https://prove2.me/theorems/c1499d86-73aa-45b6-a28f-7dffd6e08a7f
-- title:
--   Lemma 4.15 — Projected KKT tangent estimate under the strict Mangasarian–Fromovitz condition
-- statement:
--   Let $D=(F,f,G,g)$ satisfy the standing $C^2$ assumptions, with convex lower objective and constraint sections and exact KKT characterization $y\in S(x)\iff y\in K(x),\ \Lambda(x,y)\ne\varnothing$. Fix a bilevel feasible pair $z$ and $\bar\lambda\in\Lambda(z)$ satisfying (4.9): every $\mu$ with $\sum_i\mu_i\nabla_y g_i(z)=0$, $\mu_i=0$ off $\bar I^g$, and $\mu_i\ge0$ on $I^{00}$ must be zero. Define $L=f+\bar\lambda^Tg$ and the three index sets by the signs of $(\bar\lambda_i,g_i(z))$. Then
--
--   $$T_M(z)\subseteq\Pi\{(d,\delta_\lambda): DG_i(z)d\le0\ (i\in\bar I^G),\quad D(\nabla_yL)(z)d+\sum_i(\delta_\lambda)_i\nabla_yg_i(z)=0,\quad(\delta_\lambda)_i=0\ (i\in I^{0-}),\quad Dg_i(z)d=0\ (i\in I^{+0}),\quad 0\le(\delta_\lambda)_i\perp Dg_i(z)d\le0\ (i\in I^{00})\}.$$
--
--   Here $d=(\delta_x,\delta_y)$, $\Pi(d,\delta_\lambda)=d$, and perpendicularity denotes zero componentwise product. This support preserves every branch of the projected KKT cone. Assumption 4.14 is expressed through its convexity and exact KKT consequence.
--
--   Differences from the source:
--   - encoding: Euclidean coordinates and gradients, indexed from 1 → published E and Y spaces, uncurried pairs, Fin indices from 0, and Fréchet derivatives or partial Euclidean gradients; reason: the same finite-dimensional data; derivative evaluation equals the gradient pairing under Standing D
--   - generalization: convex lower data and a lower CQ everywhere on gph K (Assumption 4.14) → convex lower data and exact global KKT equivalence, without selecting a named CQ; reason: the source immediately states this consequence on p. 16 and uses it to identify M as the projected KKT set; the weaker premise includes every source instance
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, p. 16, Lemma 4.15

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_Complementarity
open scoped Topology

namespace BilevelSOC.SecondOrder.Supplement
theorem lemma_4_15 {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m)
    (lam : Fin q → ℝ) (hStanding : Standing D) (hfeas : z ∈ feasSet D)
    (hconvexCQ : ConvexKKTExact D) (hlam : lam ∈ multipliers D z)
    (hstrict : StrictMFCQ D z lam) :
    tangentCone (feasSet D) z ⊆ projection '' kktLinCone D z lam := by sorry
end BilevelSOC.SecondOrder.Supplement
