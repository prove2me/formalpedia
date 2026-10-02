-- Prove2me | Theorems.Thm_Disjunctive_CutCorrespondence_basis_correspondence
-- name    : Disjunctive.CutCorrespondence.basis_correspondence
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:46:45.501381+00:00
-- url     : https://prove2.me/theorems/d1a07b02-4164-4ee8-abf9-49aadf01de36
-- title:
--   Lemma 8.2 — the nonsingular-submatrix structure of a basic solution
-- statement:
--   This is Lemma 8.2 of Balas's *Disjunctive Programming*, cited to [33]: a basic
--   solution's basic `u`/`v`-index sets `M1,M2` are disjoint, and the `n×n` submatrix of `Ã` they
--   jointly index is nonsingular.
--
--   The book's proof eliminates the free-sign `α,β` from the reduced system (8.2) to get (8.3), an
--   `n+2`-equation system with unique solution `(ūM1,ū0,v̄M2,v̄0)`; if the submatrix were singular, a
--   second, distinct solution to (8.3) could be constructed, contradicting uniqueness — hence `Â` is
--   nonsingular, and `|M1∩M2|≠∅` would itself force `Â` singular, so `M1,M2` are disjoint.
--
--   **Formalization Note.** Nonsingularity of the submatrix indexed by a bare `Finset M` is stated via
--   the existence of an enumeration `ι` witnessing it (independent of enumeration order, since a row
--   permutation cannot turn a nonsingular matrix singular).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 98, Lemma 8.2

import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau

namespace Disjunctive.CutCorrespondence

/-- Lemma 8.2 (Balas §8.1, p. 98, [33]): in a basic solution to `(8.1)` with `u0,v0>0` and
`(α,β)` basic, whose basic `u`/`v`-components are indexed by `M1`/`M2`, `M1` and `M2` are
disjoint and the `n×n` submatrix of `Ã` indexed by `M1 ∪ M2` is nonsingular. The solution is **basic**, not merely feasible with the given supports: support containment alone is false (one row `x ≥ 1/2` in `n = 1` with `u = 0.3`, `v = 0.1`, `u₀ = v₀ = 0.1` satisfies the hypotheses, `M1`/`M2` are not disjoint and Theorem 8.4A yields `x ≥ 3/4` instead of `x ≥ 1`). -/
theorem basis_correspondence {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (M1 M2 : Finset M)
    (hbasic : IsBasicCGLPKSolution Atil btil k α u u0 v v0 β) (hu0 : 0 < u0) (hv0 : 0 < v0)
    (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0) :
    Disjoint M1 M2 ∧ IsNonsingularSubmatrix Atil (M1 ∪ M2) := by sorry

end Disjunctive.CutCorrespondence
