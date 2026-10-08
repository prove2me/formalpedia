-- Prove2me | Theorems.Thm_Disjunctive_SimplexTableau_reduced_cost_formulas_v2
-- name    : Disjunctive.SimplexTableau.reduced_cost_formulas_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:10:17.909096+00:00
-- url     : https://prove2.me/theorems/3e6fce0d-5165-4b22-a73b-6e661a6ca0a1
-- title:
--   Theorem 9.2 — reduced costs of the CGLP columns $u_i, v_i$ in terms of the LP simplex tableau
-- statement:
--   Let $(\alpha,\beta,u,u_0,v,v_0)$ be a basic feasible solution of $(CGLP)_k$ with $u_0,v_0>0$, whose basic $u$- and $v$-components are the rows $\iota(j)$, $j\in M_1$, resp. $j\in M_2$, where $M_1\sqcup M_2$ is the set of row positions of the nonsingular $\hat A=\tilde A_J$, $J=\iota(\{1,\dots,n\})$. Let $\bar x$ be the point to be cut off, $\bar s=\tilde A\bar x-\tilde b$, and $\bar a_{ij}$, $\bar a_{i0}$ the tableau coefficients of a row $i\notin J$. Then the reduced costs of the nonbasic columns $u_i$ and $v_i$ are
--   $$r_{u_i}=\sigma\Big(-\sum_{j\in M_1}\bar a_{ij}+\sum_{j\in M_2}\bar a_{ij}-1\Big)-\sum_{j\in M_2}\bar a_{ij}\bar s_j+\bar a_{i0}(1-\bar x_k),$$
--   $$r_{v_i}=\sigma\Big(\sum_{j\in M_1}\bar a_{ij}-\sum_{j\in M_2}\bar a_{ij}-1\Big)-\sum_{j\in M_1}\bar a_{ij}\bar s_j+\bar a_{i0}\bar x_k,$$
--   with $\sigma=\big(\sum_{j\in M_2}\bar a_{kj}\bar s_j-\bar a_{k0}(1-\bar x_k)\big)/\big(1+\sum_{j\in J}|\bar a_{kj}|\big)$ the current objective value: the objective $\alpha\bar x-\beta$ of the solution obtained by giving $u_i,v_i$ the values $u_i,v_i$ and adjusting the basic variables by (9.7)-(9.9) equals $\sigma+u_ir_{u_i}+v_ir_{v_i}$.
--
--   **Formalization Note.** The retired version used a transcription of (9.6) in which the entire expression was multiplied by $\sigma$; with that reading the asserted decomposition is false (e.g. $n=1$, rows $x\ge 1/2$ and $x\ge 0$, $\bar x=0.3$). The reduced costs are now as above. As in the retired version, the objective of the extended solution (`ObjExt`) is built independently from (9.7)-(9.9), so the identity is genuine content. The solution is assumed basic (an extreme point of the feasible set of (8.1)) and $u,v$ vanish outside the basic rows $\iota(M_1)$, $\iota(M_2)$, as for a basic solution in the book (the retired version allowed nonzero multipliers on rows outside $J$).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §9.1, p. 109-113, Theorem 9.2, eq. (9.6)

import Mathlib
import Definitions.Def_Disjunctive_SimplexTableau_Cglp
import Definitions.Def_Disjunctive_SimplexTableau_Tableau
import Definitions.Def_Disjunctive_SimplexTableau_ReducedCost_v2

namespace Disjunctive.SimplexTableau

/-- Theorem 9.2 (Balas, *Disjunctive Programming*, §9.1, p. 109-113): let `(α,β,u,u0,v,v0)` be a
basic feasible solution of `(CGLP)_k` with `u0, v0 > 0` whose basic `u`/`v`-components are the
rows `ι j`, `j ∈ M1`, resp. `j ∈ M2` (`M1, M2` partition the row-positions of the nonsingular
`Â = Ã_J`). For a row `i ∉ J`, the objective `αx̄ - β` of the solution obtained by bringing
`u_i, v_i` into the solution (eqs. (9.7)-(9.9)) equals `σ + u_i r_{u_i} + v_i r_{v_i}`, i.e.
`r_{u_i}, r_{v_i}` of eq. (9.6) are the reduced costs of the columns `u_i, v_i`.

Corrected from the retired version: in `ReducedCostU/V` only the bracket
`(∓∑_{M1} ā_ij ± ∑_{M2} ā_ij - 1)` is multiplied by `σ` (the retired formulas multiplied the whole
expression by `σ`, which made the identity false, e.g. `n = 1`, rows `x ≥ 1/2`, `x ≥ 0`); the
solution is basic (an extreme point of `(8.1)`) and `u`, `v` vanish off the basic rows, as for a
basic solution of the book. -/
theorem reduced_cost_formulas_v2 {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ)
    (M1 M2 : Finset (Fin n)) (ι : Fin n → M)
    (hbasic : (α, u, u0, v, v0, β) ∈ Set.extremePoints ℝ
      {w : (Fin n → ℝ) × (M → ℝ) × ℝ × (M → ℝ) × ℝ × ℝ |
        IsCGLPKFeasible Atil btil k w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2})
    (hu0 : 0 < u0) (hv0 : 0 < v0)
    (hu_supp : ∀ ρ : M, u ρ ≠ 0 → ∃ j ∈ M1, ι j = ρ)
    (hv_supp : ∀ ρ : M, v ρ ≠ 0 → ∃ j ∈ M2, ι j = ρ)
    (hι_inj : Function.Injective ι) (hnonsing : IsUnit (Ahat Atil ι).det)
    (hM_disj : Disjoint M1 M2) (hM_cover : M1 ∪ M2 = Finset.univ)
    (i : M) (hi : ∀ j : Fin n, ι j ≠ i) (xbar : Fin n → ℝ) (ui vi : ℝ) :
    ObjExt Atil btil ι k M1 M2 i xbar ui vi =
      SigmaCoef Atil btil ι k M1 M2 xbar + ui * ReducedCostU Atil btil ι k M1 M2 xbar i +
        vi * ReducedCostV Atil btil ι k M1 M2 xbar i := by sorry

end Disjunctive.SimplexTableau
