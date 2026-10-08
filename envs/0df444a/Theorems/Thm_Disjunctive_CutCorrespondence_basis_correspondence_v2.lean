-- Prove2me | Theorems.Thm_Disjunctive_CutCorrespondence_basis_correspondence_v2
-- name    : Disjunctive.CutCorrespondence.basis_correspondence_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:07:13.155757+00:00
-- url     : https://prove2.me/theorems/8549f362-9af4-4ae9-9e47-649b380de399
-- title:
--   Lemma 8.2 — the basic index sets $M_1,M_2$ of a $(CGLP)_k$ basis are disjoint and index a nonsingular submatrix
-- statement:
--   Let $\tilde Ax\ge\tilde b$ be the LP relaxation of a mixed 0-1 program (it contains the rows $x_j\ge 0$ for all $j$ and $-x_j\ge -1$ for $j\in N'$), and let $(\alpha,\beta,u,u_0,v,v_0)$ be a basic solution of the cut-generating LP $(CGLP)_k$ (8.1) with $u_0>0$, $v_0>0$, whose basic $u$- and $v$-components are indexed by $M_1$ and $M_2$ (in a basis in which $\alpha,\beta,u_0,v_0$ are basic). Then
--   $$M_1\cap M_2=\emptyset,$$
--   and the $n\times n$ submatrix $\hat A$ of $\tilde A$ whose rows are indexed by $M_1\cup M_2$ is nonsingular.
--
--   **Formalization Note.** The retired version only required $M_1,M_2$ to contain the supports of $u,v$, so $M_1=M_2=$ all rows was admissible and disjointness failed (one row $x\ge 1/2$, $n=1$). Here $M_1,M_2$ are the index sets of a genuine basis (`IsCGLPKBasis`: $|M_1|+|M_2|=n$ and the columns of $\alpha,\beta,u_0,v_0,u_{M_1},v_{M_2}$ are linearly independent), "basic solution" is an extreme point of the bounded feasible polytope of (8.1), and the chapter's standing assumption on $\tilde Ax\ge\tilde b$ (bound rows present) is stated explicitly. Nonsingularity of a submatrix indexed by a set of rows is expressed via some enumeration of the rows.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §8.1, p. 98, Lemma 8.2

import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp_v2
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau_v2

namespace Disjunctive.CutCorrespondence

/-- Lemma 8.2 (Balas, *Disjunctive Programming*, §8.1, p. 98, [33]): let `(α,β,u,u0,v,v0)` be a
basic solution of `(CGLP)_k` (8.1) with `u0, v0 > 0`, and let the basic components of `u` and `v`
be indexed by `M1` and `M2` (`IsCGLPKBasis`: `α, β, u0, v0, u_{M1}, v_{M2}` are the basic
columns). Then `M1 ∩ M2 = ∅` and the `n×n` submatrix of `Ã` with rows `M1 ∪ M2` is nonsingular.

Corrected from the retired version, which only required `M1`, `M2` to *contain* the supports
of `u`, `v` (so `M1 = M2 = univ` was allowed); `M1`, `M2` are now the index sets of a genuine
basis. The section's standing assumption that `Ãx ≥ b̃` contains `x ≥ 0` and `x_j ≤ 1`
(`j ∈ N'`) is stated explicitly. -/
theorem basis_correspondence_v2 {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (Nprime : Finset (Fin n))
    (hsys : IsMixedZeroOneSystem Atil btil Nprime) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (M1 M2 : Finset M)
    (hbasic : IsBasicCGLPKSolution Atil btil k α u u0 v v0 β) (hu0 : 0 < u0) (hv0 : 0 < v0)
    (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0)
    (hbasis : IsCGLPKBasis Atil btil k M1 M2) :
    Disjoint M1 M2 ∧ IsNonsingularSubmatrix Atil (M1 ∪ M2) := by sorry

end Disjunctive.CutCorrespondence
