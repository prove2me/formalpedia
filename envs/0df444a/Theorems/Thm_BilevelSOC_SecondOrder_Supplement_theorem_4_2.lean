-- Prove2me | Theorems.Thm_BilevelSOC_SecondOrder_Supplement_theorem_4_2
-- name    : BilevelSOC.SecondOrder.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:42:36.883208+00:00
-- url     : https://prove2.me/theorems/b19f1f78-dab4-4b7f-85d4-fb26aedede2d
-- title:
--   Theorem 4.2 — Value-function sufficient condition using the upper Dini derivative
-- statement:
--   Let $D=(F,f,G,g)$ satisfy the standing $C^2$ assumptions, and let $z=(\bar x,\bar y)$ be feasible for the optimistic bilevel program. Write $K(x)=\{y:g(x,y)\le0\}$, $S(x)=\arg\min_{K(x)} f(x,\cdot)$, $M=\{(x,y):G(x,y)\le0,\ y\in S(x)\}$, and $\varphi(x)=\inf_{K(x)} f(x,\cdot)$. Assume $K$ is locally bounded at $\bar x$ and LMFCQ holds at every $(\bar x,y)$ with $y\in S(\bar x)$. If the only direction $d=(\delta_x,\delta_y)$ satisfying
--
--   $$DF(z)d\le0,\quad DG_i(z)d\le0\ (i\in\bar I^G),\quad Df(z)d-\varphi^+(\bar x;\delta_x)\le0,\quad Dg_i(z)d\le0\ (i\in\bar I^g)$$
--
--   is zero, then $z$ is a strict local minimizer of $F$ on $M$. Here active indices are exactly the zero constraints, and $\varphi^+$ is the upper Dini derivative, without an assumed ordinary derivative. This companion criterion treats the value-function reformulation.
--
--   Differences from the source:
--   - encoding: Euclidean coordinates and gradients, indexed from 1 → published E and Y spaces, uncurried pairs, Fin indices from 0, and Fréchet derivatives or partial Euclidean gradients; reason: the same finite-dimensional data; derivative evaluation equals the gradient pairing under Standing D
--   - encoding: upper Dini value derivative φ⁺ → EReal limsup of positive-step directional quotients of valueFn; reason: no directional differentiability assumption is added and no real unbounded-supremum default is used
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, p. 10, Theorem 4.2

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_Multipliers
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_ValueCriteria
open scoped Topology

namespace BilevelSOC.SecondOrder.Supplement
theorem theorem_4_2 {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m)
    (hStanding : Standing D) (hfeas : z ∈ feasSet D)
    (hbounded : LowerLocallyBounded D z.1)
    (hMFCQ : ∀ y ∈ solMap D z.1, LMFCQ D (z.1, y))
    (hexclude : ∀ d, valueSystem D z d → d = 0) :
    StrictLocalMin D.F (feasSet D) z := by sorry
end BilevelSOC.SecondOrder.Supplement
