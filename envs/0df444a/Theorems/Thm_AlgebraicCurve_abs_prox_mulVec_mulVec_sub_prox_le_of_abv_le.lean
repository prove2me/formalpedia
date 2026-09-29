-- Prove2me | Theorems.Thm_AlgebraicCurve_abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le
-- name    : AlgebraicCurve.abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/9a26b0bf-b886-5868-b430-e97c79c49633
-- title:
--   Bounded change of basis shifts chordal proximity by at most 4logβ
-- statement:
--   Let $K$ be a field and $\mu$ a real-valued absolute value on $K$ which is non-archimedean, i.e. satisfies the ultrametric inequality. Let $r$ be a natural number, let $M, M^{\mathrm{inv}}$ be $r\times r$ matrices over $K$ with $M^{\mathrm{inv}}M = 1$, and let $\beta$ be a real number with $1\le\beta$ such that $\mu(M_{ij})\le\beta$ and $\mu(M^{\mathrm{inv}}_{ij})\le\beta$ for all indices $i,j$. Let $x,y \colon \mathrm{Fin}\,r \to K$ be two vectors, both nonzero as functions, and assume that some $2\times 2$ minor $x_i y_j - x_j y_i$ is nonzero. Writing, for vectors $u,v$,
--   $$\operatorname{prox}_\mu(u,v) = \log\Big(\sup_i \mu(u_i)\Big) + \log\Big(\sup_i \mu(v_i)\Big) - \log\Big(\sup_{(i,j)} \mu(u_i v_j - u_j v_i)\Big),$$
--   the conclusion is the two-sided bound
--   $$\big|\operatorname{prox}_\mu(Mx, My) - \operatorname{prox}_\mu(x,y)\big| \le 4\log\beta,$$
--   where $Mx$ and $My$ denote the matrix–vector products. Only the one-sided relation $M^{\mathrm{inv}}M=1$ is assumed; $M^{\mathrm{inv}}$ enters solely through its entry bound and this relation.
--
--   This is the invariance, up to an explicit additive budget, of the chordal proximity $\operatorname{prox}_\mu$ of a pair of vectors under a linear change of coordinates whose matrix and whose left inverse have entries of absolute value at most $\beta$. It is used to transfer proximity comparisons between different bases, e.g. in the chart-comparison estimates for components of algebraic curves and in the covering estimates for modular curves that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le.lean

import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ) {r : ℕ}
    (M Minv : Matrix (Fin r) (Fin r) K) (hM : Minv * M = 1)
    (β : ℝ) (hβ : 1 ≤ β) (hMβ : ∀ i j, μ (M i j) ≤ β) (hMβ' : ∀ i j, μ (Minv i j) ≤ β)
    (x y : Fin r → K) (hx : x ≠ 0) (hy : y ≠ 0) (h : ∃ i j, x i * y j - x j * y i ≠ 0) :
    |prox μ (M.mulVec x) (M.mulVec y) - prox μ x y| ≤ 4 * Real.log β := by sorry
