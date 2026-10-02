-- Prove2me | Theorems.Thm_Disjunctive_NormalForms_elementary_disjunction_hull
-- name    : Disjunctive.NormalForms.elementary_disjunction_hull
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:28:11.489476+00:00
-- url     : https://prove2.me/theorems/a444942c-300e-48df-b90d-ae2e578ae082
-- title:
--   Theorem 4.4 — the hull of an elementary disjunctive set
-- statement:
--   This is Theorem 4.4 of Balas's *Disjunctive Programming*: the closed convex hull of a union
--   of halfspaces is either everything or nothing new.
--
--   Let $F = \bigcup_{i \in Q} H_i^+$ for halfspaces $H_i^+ = \{x : a_i x \ge a_{i0}\}$. If $F$ is
--   **proper** (no single $H_k^+$ already contains every other $H_i^+$, i.e. $F \ne H_k^+$ for every
--   $k$), then $\mathrm{cl}\,\mathrm{conv}(F) = \mathbb{R}^n$. If $F$ is **improper** ($F = H_k^+$
--   for some $k$), then $\mathrm{cl}\,\mathrm{conv}(F) = H_k^+$.
--
--   In other words, taking the convex hull of a *proper* elementary disjunctive set discards every
--   constraint that defines it — replacing such a disjunction with its convex hull is equivalent to
--   deleting it entirely. This is exactly why, in the hull-relaxation hierarchy of Theorem 4.7, the
--   proper elementary disjunctions of a CNF contribute nothing to `h-rel` at the CNF level (Lemma
--   4.5), and only the *improper* conjuncts (already polyhedra) survive.
--
--   **Formalization Note.** "Improper" is spelled out via `∃ k, F = H_k^+` (the union literally equals
--   one of its own halfspaces); "proper" is its negation.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 51, Theorem 4.4

import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

namespace Disjunctive.NormalForms

/-- Theorem 4.4 (Balas §4.2, p. 51): the closed convex hull of an elementary disjunctive set
(a union of halfspaces) is all of `ℝⁿ` if it is proper, and the halfspace itself if it is
improper. Stated for a nonempty index set: with `Q = ∅` the union is `∅`, no `k` exists,
and the first clause would assert `cl conv ∅ = ℝⁿ`. -/
theorem elementary_disjunction_hull {n : ℕ} {Q : Type*} [Fintype Q] [Nonempty Q]
    (d : Q → Fin n → ℝ)
    (d0 : Q → ℝ) :
    ((¬ ∃ k, (⋃ i : Q, HalfspaceGE (d i) (d0 i)) = HalfspaceGE (d k) (d0 k)) →
        closure (convexHull ℝ (⋃ i : Q, HalfspaceGE (d i) (d0 i))) = Set.univ) ∧
      (∀ k, (⋃ i : Q, HalfspaceGE (d i) (d0 i)) = HalfspaceGE (d k) (d0 k) →
        closure (convexHull ℝ (⋃ i : Q, HalfspaceGE (d i) (d0 i))) = HalfspaceGE (d k) (d0 k)) := by sorry

end Disjunctive.NormalForms
