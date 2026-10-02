-- Prove2me | Theorems.Thm_Disjunctive_SimplexTableau_reduced_cost_formulas
-- name    : Disjunctive.SimplexTableau.reduced_cost_formulas
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:52:39.611684+00:00
-- url     : https://prove2.me/theorems/92f2ba05-0bc7-47ef-9894-15fb6d8d541d
-- title:
--   Theorem 9.2 — reduced-cost formulas for the CGLP columns
-- statement:
--   This is Theorem 9.2 of Balas's *Disjunctive Programming*: for a basic feasible
--   `(CGLP)_k` solution, the reduced costs of the nonbasic columns `u_i,v_i` (`i∉J∪{k}`) are given by
--   eq. (9.6), in terms of the tableau coefficients `ā_kj,ā_ij` (`j∈J∪{0}`).
--
--   The book's proof restricts `(8.1)` to the basic variables plus `u_i,v_i`, eliminates `α,β` to get
--   `(uM1,-vM2)ÃJ+(ui-vi)Ãi=(u0+v0)ek` and its `b̃`-analogue, substitutes Lemma 9.1's tableau
--   coefficients, solves for `uj,vj,v0` (eq. (9.8)) and `u0+v0` (eq. (9.9)) as functions of `ui,vi`,
--   computes the objective `αx̄-β=vM2s̄M2+vis̄i+v0(x̄k-1)`, and reads off `rui,rvi` as the coefficients
--   of `ui,vi` in the resulting expression.
--
--   **Formalization Note.** `ObjExt` (the objective at the pivoted-out extension) is built
--   independently via the same substitution chain (9.7)-(9.9) the book's proof follows, not by
--   definition from `ReducedCostU`/`ReducedCostV`, so the theorem's assertion that they coincide is
--   genuine content, matching "we can then read the reduced costs... as the coefficients."
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 109, Theorem 9.2

import Mathlib
import Definitions.Def_Disjunctive_SimplexTableau_Cglp
import Definitions.Def_Disjunctive_SimplexTableau_Tableau
import Definitions.Def_Disjunctive_SimplexTableau_ReducedCost

namespace Disjunctive.SimplexTableau

/-- Theorem 9.2 (Balas §9.1, p. 109-113): for a basic feasible solution to `(CGLP)_k` (with
`u0,v0>0`, `α,β` basic, basic `u`/`v`-components indexed by row-positions `M1,M2`, `Â` the
resulting nonsingular submatrix), the objective value of the solution obtained by pivoting a row
`i ∉ J` out of the basis with multiplier values `u_i,v_i` decomposes as `σ + u_i·r_ui + v_i·r_vi`
— i.e. `r_ui,r_vi` (eq. (9.6)) are exactly the reduced costs (the coefficients of `u_i,v_i` in
this decomposition). `M1` and `M2` partition the row positions, which is what basicness of the
solution means here (Lemma 8.2) and what Theorem 10.1 of `10-split-closure` already assumes:
without it the `v_i` coefficient is off by `ā_{i1} s̄_1` (`n = 2`, `Â = I`, `M1 = {0}`,
`M2 = ∅`). -/
theorem reduced_cost_formulas {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ)
    (M1 M2 : Finset (Fin n)) (ι : Fin n → M)
    (hfeas : IsCGLPKFeasible Atil btil k α u u0 v v0 β) (hu0 : 0 < u0) (hv0 : 0 < v0)
    (hu_supp : ∀ j : Fin n, j ∉ M1 → u (ι j) = 0) (hv_supp : ∀ j : Fin n, j ∉ M2 → v (ι j) = 0)
    (hι_inj : Function.Injective ι) (hnonsing : IsUnit (Ahat Atil ι).det)
    (hM_disj : Disjoint M1 M2) (hM_cover : M1 ∪ M2 = Finset.univ)
    (i : M) (hi : ∀ j : Fin n, ι j ≠ i) (xbar : Fin n → ℝ) (ui vi : ℝ) :
    ObjExt Atil btil ι k M1 M2 i xbar ui vi =
      SigmaCoef Atil btil ι k M1 M2 xbar + ui * ReducedCostU Atil btil ι k M1 M2 xbar i +
        vi * ReducedCostV Atil btil ι k M1 M2 xbar i := by sorry

end Disjunctive.SimplexTableau
