-- Prove2me | Theorems.Thm_AlgebraicCurve_prox_smul_smul
-- name    : AlgebraicCurve.prox_smul_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/bde08055-f094-58d5-82b6-853daee02cf0
-- title:
--   Scaling invariance of chordal proximity
-- statement:
--   Let $K$ be a field and $\mu : K \to \mathbb{R}$ an absolute value, let $r$ be a natural number, and let $x, v : \mathrm{Fin}\,r \to K$ be two rows of length $r$. Let $c, d \in K$ with $c \neq 0$ and $d \neq 0$, and assume the nondegeneracy hypothesis that $\sup_{(l,m)} \mu(x_l v_m - x_m v_l) \neq 0$, the supremum being taken over all pairs $(l,m) \in \mathrm{Fin}\,r \times \mathrm{Fin}\,r$. Then the chordal proximity of the rescaled rows agrees with that of the original rows: $\operatorname{prox}_\mu(c \cdot x, d \cdot v) = \operatorname{prox}_\mu(x, v)$, where by definition $$\operatorname{prox}_\mu(x,v) = \log\Big(\sup_l \mu(x_l)\Big) + \log\Big(\sup_l \mu(v_l)\Big) - \log\Big(\sup_{(l,m)} \mu(x_l v_m - x_m v_l)\Big),$$ the scalar multiplications $c \cdot x$ and $d \cdot v$ being componentwise. All suprema are the real-valued suprema over the finite index types, and the logarithm is the Mathlib real logarithm, so the identity is an identity of real numbers.
--
--   This records that the chordal proximity of a pair of rows depends only on their classes in projective space, i.e. is invariant under rescaling each row by a nonzero scalar, provided the two rows are not proportional (the guard $\sup \mu(x_l v_m - x_m v_l) \neq 0$, without which the subtracted term degenerates to $\log 0 = 0$ and the identity fails). It is used when passing between different normalisations of value rows, and is cited by the chart-comparison and pivot lemmas for component charts and for the modular curve $J_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_prox_smul_smul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.prox_smul_smul
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) {r : ℕ}
    (x v : Fin r → K) {c d : K} (hc : c ≠ 0) (hd : d ≠ 0)
    (h : (⨆ p : Fin r × Fin r, μ (x p.1 * v p.2 - x p.2 * v p.1)) ≠ 0) :
    prox μ (c • x) (d • v) = prox μ x v := by sorry
