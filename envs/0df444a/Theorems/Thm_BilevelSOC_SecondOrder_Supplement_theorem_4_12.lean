-- Prove2me | Theorems.Thm_BilevelSOC_SecondOrder_Supplement_theorem_4_12
-- name    : BilevelSOC.SecondOrder.Supplement.theorem_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:49:55.484369+00:00
-- url     : https://prove2.me/theorems/41b0e7a5-731f-4cd2-92ab-9a94ce166ad4
-- title:
--   Theorem 4.12 — Convex fixed lower feasible set and normal-cone variational criterion
-- statement:
--   Let $D=(F,f,G,g)$ satisfy the standing $C^2$ assumptions and Assumption 4.10: $f(x,\cdot)$ is convex for every $x$, while $g$ is independent of $x$ and componentwise convex. Fix a bilevel feasible $z=(\bar x,\bar y)$ and let $L_K(\bar y)$ be the active lower-constraint linearization cone. For every $u\in L_K(\bar y)\setminus\{0\}$ and every $\lambda\in\mathbb R^q$, assume
--
--   $$\sum_i\lambda_i\nabla g_i(\bar y)=0,\quad\lambda\ge0,\quad\lambda^Tg(\bar y)=0,\quad\sum_i\lambda_i u^T\nabla^2g_i(\bar y)u\ge0\quad\Longrightarrow\quad\lambda=0.$$
--
--   Suppose there is no solution with $d=(\delta_x,\delta_y)\ne0$ to the following system, where $\lambda,\mu\in\mathbb R^q$ are independent and $\kappa\in\mathbb R$ is unrestricted:
--
--   $$\begin{gathered}DF(z)d\le0,\quad DG_i(z)d\le0\ (i\in\bar I^G),\\
--   \nabla^2_{yx}f(z)\delta_x+\nabla^2_{yy}f(z)\delta_y+\kappa\nabla_y f(z)+\sum_i[\lambda_i\nabla^2g_i(\bar y)\delta_y+\mu_i\nabla g_i(\bar y)]=0,\\
--   \nabla_yf(z)+\sum_i\lambda_i\nabla g_i(\bar y)=0,\quad\lambda\ge0,\quad\lambda^Tg(\bar y)=0,\\
--   \mu\ge0,\quad\mu^Tg(\bar y)=0,\quad\sum_i\mu_iDg_i(\bar y)\delta_y=0,\\
--   Dg_i(\bar y)\delta_y\le0\ (i\in\bar I^g),\quad D_yf(z)\delta_y=0.
--   \end{gathered}$$
--
--   Then $z$ is a strict local minimizer of the bilevel program. This variational companion excludes nonzero primal directions; nonzero auxiliary multipliers with zero primal direction do not violate its premise.
--
--   Differences from the source:
--   - encoding: Euclidean coordinates and gradients, indexed from 1 → published E and Y spaces, uncurried pairs, Fin indices from 0, and Fréchet derivatives or partial Euclidean gradients; reason: the same finite-dimensional data; derivative evaluation equals the gradient pairing under Standing D
--   - reading: ∇f_y in (4.7e) → the y derivative of f paired with δy; reason: the notation denotes ∇y f, consistent with the preceding critical-cone calculation and the proof on pp. 14–15
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, p. 14, Theorem 4.12

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_Multipliers
open scoped Topology

namespace BilevelSOC.SecondOrder.Supplement
theorem theorem_4_12 {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m)
    (hStanding : Standing D) (hfeas : z ∈ feasSet D)
    (hconvex : FixedConvexLower D) (habnormal : abnormalCondition D z)
    (hexclude : ∀ d lam κ μ, variationalSystem D z d lam κ μ → d = 0) :
    StrictLocalMin D.F (feasSet D) z := by sorry
end BilevelSOC.SecondOrder.Supplement
