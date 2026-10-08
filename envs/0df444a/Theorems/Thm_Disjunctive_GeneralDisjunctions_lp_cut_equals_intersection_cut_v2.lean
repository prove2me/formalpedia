-- Prove2me | Theorems.Thm_Disjunctive_GeneralDisjunctions_lp_cut_equals_intersection_cut_v2
-- name    : Disjunctive.GeneralDisjunctions.lp_cut_equals_intersection_cut_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:35.686298+00:00
-- url     : https://prove2.me/theorems/5db3d169-e82f-4132-9354-2bd0697d3fcc
-- title:
--   Theorem 11.9 — a basic CGLP solution supported on one nonsingular cobasis yields an intersection cut
-- statement:
--   Let $(\alpha,\beta,\{u^t,u^t_0\}_{t\in T})$ be a basic feasible solution of the CGLP (11.6) with $u^t_0>0$ for all $t\in T$. If there is a nonsingular $n\times n$ submatrix $\hat A=\tilde A_J$ of $\tilde A$ such that $u^t_j=0$ for all $j\notin J$ and $t\in T$, and the basic solution $\bar a_0=\hat A^{-1}\hat b$ of the LP basis with nonbasic set $J$ lies in the interior of $S=\{x: d^tx\le d^t_0,\ t\in T\}$, then the lift-and-project cut $\alpha x\ge\beta$ is equivalent to the intersection cut $\pi x_J\ge 1$ from $S$ and the simplex tableau with nonbasic set $J$, where
--   $$\pi_j=\max_{t\in T}\pi^t_j,\qquad \pi^t_j=\frac{d^t(-\bar a_j)}{d^t_0-d^t\bar a_0},$$
--   and $x_J=\hat Ax-\hat b$ are the surplus variables of the rows $J$: $\{x:\alpha x\ge\beta\}=\{x:\pi(\hat Ax-\hat b)\ge 1\}$.
--
--   **Formalization Note.** The retired version assumed only a *feasible* solution of (11.6), which does not determine the cut (refuted by $u=u_0=1/2$ for the single term $x\ge 1$ and row $x\ge 0$); the book's theorem is about basic feasible solutions, here extreme points of the feasible polytope of (11.6). The requirement $\bar a_0\in\operatorname{int}S$ is the condition under which the intersection cut from $S$ and that tableau is defined (Theorem 1.1; Balas–Kis's proof uses "$d^t_0-d^t\bar a_0>0$ since $\bar a_0\in\operatorname{int}S$"); without it the statement fails even for basic solutions (e.g. $n=1$, row $x\ge 3$, terms $x\ge 1$, $x\ge 2$).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §11.5, p. 162, Theorem 11.9 (= Balas–Kis 2016, Theorem 9)

import Mathlib
import Definitions.Def_Disjunctive_GeneralDisjunctions_Cglp_v2

namespace Disjunctive.GeneralDisjunctions

/-- Theorem 11.9 (Balas, *Disjunctive Programming*, §11.5, p. 162; Balas–Kis 2016, Theorem 9):
let `(α, β, {uᵗ, uᵗ₀})` be a basic feasible solution of the CGLP (11.6) with `uᵗ₀ > 0` for all
`t ∈ T`. If there is a nonsingular `n×n` submatrix `Ã_J` of `Ã` (rows `ι`) such that `uᵗ_j = 0`
for all `j ∉ J`, `t ∈ T`, then the L&P cut `αx ≥ β` is equivalent to the intersection cut
`πx_J ≥ 1` from `S = {x : dᵗx ≤ dᵗ₀, t ∈ T}` and the LP simplex tableau with nonbasic set `J`
(expressed through the surplus variables `x_J = s_J(x)` of the rows `ι`).

Corrected from the retired version: the solution is *basic* (an extreme point of (11.6)), not
merely feasible (a feasible solution does not determine the cut); and the intersection cut from
`S` and the tableau of `J` is only defined when the basic solution `ā0` lies in `int S`
(`BasicSolutionInIntS`, the standing requirement of Theorem 1.1 used in the book's proof: "the
right-hand side is positive since `ā0 ∈ int S`"). -/
theorem lp_cut_equals_intersection_cut_v2 {n : ℕ} {M T : Type*} [Fintype M] [Fintype T]
    [Nonempty T] [DecidableEq M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (d : T → Fin n → ℝ) (d0 : T → ℝ)
    (α : Fin n → ℝ) (β : ℝ) (u : T → M → ℝ) (u0 : T → ℝ)
    (hbasic : IsBasicCGLP116Solution Atil btil d d0 α u u0 β)
    (hu0pos : ∀ t, 0 < u0 t)
    (ι : Fin n → M) (hι_inj : Function.Injective ι)
    (hnonsing : IsUnit (Ahat Atil ι).det)
    (hsupp : ∀ t, ∀ i, i ∉ Finset.image ι Finset.univ → u t i = 0)
    (hint : BasicSolutionInIntS Atil btil ι d d0) :
    {x | β ≤ dotProduct α x} = IntersectionCutFromS Atil btil ι d d0 := by sorry

end Disjunctive.GeneralDisjunctions
