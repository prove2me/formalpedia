-- Prove2me | Theorems.Thm_Disjunctive_CutCorrespondence_cglpk_basicness
-- name    : Disjunctive.CutCorrespondence.cglpk_basicness
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:46:11.943469+00:00
-- url     : https://prove2.me/theorems/5da6ccd6-ac00-4fca-ae83-d30d973f8f05
-- title:
--   Lemma 8.1 — basicness forces u0, v0 positive
-- statement:
--   This is Lemma 8.1 of Balas's *Disjunctive Programming*: in any basic solution to
--   `(CGLP)_k` yielding an undominated cut, both `u0` and `v0` must be positive.
--
--   The book's own one-line proof: if `u0=0` then `α=uÃ, β=ub̃`, and if `v0=0` then `α=vÃ,β=vb̃` — in
--   either case `αx≥β` is *literally* a nonnegative combination of `Ãx≥b̃`'s own rows, i.e. dominated
--   by the LP relaxation, contradicting the hypothesis.
--
--   **Formalization Note.** "Basic solution" is formalized as an extreme point of `(8.1)`'s (bounded,
--   by the normalization constraint) feasible polytope; "not dominated" via `IsDominatedByLP`.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 97, Lemma 8.1

import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp

namespace Disjunctive.CutCorrespondence

/-- Lemma 8.1 (Balas §8, p. 97): in any basic solution to `(CGLP)_k` (8.1) that yields an
inequality `αx ≥ β` not dominated by the LP relaxation's own constraints, both `u0` and `v0`
are positive. -/
theorem cglpk_basicness {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (k : Fin n) (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ)
    (β : ℝ) (hbasic : IsBasicCGLPKSolution Atil btil k α u u0 v v0 β)
    (hnd : ¬ IsDominatedByLP Atil btil α β) : 0 < u0 ∧ 0 < v0 := by sorry

end Disjunctive.CutCorrespondence
