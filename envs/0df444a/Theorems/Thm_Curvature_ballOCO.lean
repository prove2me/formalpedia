-- Prove2me | Theorems.Thm_Curvature_ballOCO
-- name    : Curvature.ballOCO
-- status  : Proved
-- author  : @ssakaue
-- created : 2026-11-24T07:22:15.675767+00:00
-- url     : https://prove2.me/theorems/07a98199-b5c3-480a-9dbc-37a10a003331
-- title:
--   Theorem 2 — fixed-parameter guarantee for Algorithm 1 on the Euclidean unit ball
-- statement:
--   Let $d\ge1$ and $\varepsilon\in(0,1]$, and let $g_1,g_2,\ldots\in\mathbb R^d$ be arbitrary input vectors with $\lVert g_t\rVert_2\le1$; they need not be subgradients of losses. Run Algorithm 1 of the paper with parameter $\varepsilon$ on these inputs, starting from the regularizer $\frac12x^\top Bx$ with $B=(10\lceil\sqrt d\,\rceil/\varepsilon)I_d$. In round $t$, Algorithm 1 predicts $w_t\in\mathbb B_2^d$, the Euclidean projection of its internal iterate $z_t$ onto the unit ball, and then observes $g_t$. It then corrects $g_t$ when $z_t\notin\mathbb B_2^d$, moves the internal iterate using the corrected input, revokes the curvature of each quadratic regularization term whose residual has absolute value at least its threshold, and adds a new quadratic regularization term when the corrected input is nonzero. Thus $w_t$ depends only on $g_1,\ldots,g_{t-1}$.
--
--   Then Algorithm 1 is well defined in every round: each update finds the matrix inverses it needs and finishes its movement. Moreover, for every comparator $u\in\mathbb B_2^d$ and every horizon $T\ge1$,
--
--   $$
--   2\sum_{t=1}^T\langle g_t,w_t-u\rangle-\varepsilon\sum_{t=1}^T\bigl|\langle g_t,w_t-u\rangle\bigr|\le\frac{20}{\varepsilon}\bigl\lceil\sqrt d\,\bigr\rceil.
--   $$
--
--   The prediction sequence is the same for all $u$ and $T$.
-- source:
--   arXiv:2611.27572v1, Theorem 2, p. 5. https://arxiv.org/html/2611.27572v1#Thmtheorem2

import Definitions.Def_Curvature_BallState
import Definitions.Def_Curvature_GeneralRun
import Definitions.Def_Curvature_InitialCoordinates
import Definitions.Def_Curvature_Movement
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open Curvature

theorem Curvature.ballOCO (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1)
    (g : ℕ → Vec d) (hg : ∀ t, norm₂ (g t) ≤ 1) :
    ∃ s : ℕ → BallState d, (∀ t, stateAfter ε g t = some (s t)) ∧
      ∀ (u : Vec d), norm₂ u ≤ 1 → ∀ (T : ℕ), 1 ≤ T →
        let r := fun t => excess (g t) (projectBall (s t).z) u
        2 * (∑ t ∈ Finset.range T, r t) - ε * (∑ t ∈ Finset.range T, |r t|) ≤
          (20 / ε) * dimensionFactor d := by sorry
