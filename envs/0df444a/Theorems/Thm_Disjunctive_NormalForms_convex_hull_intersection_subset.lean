-- Prove2me | Theorems.Thm_Disjunctive_NormalForms_convex_hull_intersection_subset
-- name    : Disjunctive.NormalForms.convex_hull_intersection_subset
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:29:06.181351+00:00
-- url     : https://prove2.me/theorems/e3a52aae-1aa8-445c-a583-110f3a4ca185
-- title:
--   Lemma 4.6 — convexifying before an intersection can only shrink it
-- statement:
--   This is Lemma 4.6 of Balas's *Disjunctive Programming*, the fact that drives every inclusion
--   in Theorem 4.7's hierarchy.
--
--   For unions of polyhedra $S_1, S_2$:
--
--   $$
--   \mathrm{cl}\,\mathrm{conv}(S_1 \cap S_2) \subseteq (\mathrm{cl}\,\mathrm{conv}\,S_1) \cap
--   (\mathrm{cl}\,\mathrm{conv}\,S_2).
--   $$
--
--   Since $S_1 \cap S_2$ is already contained in the right-hand side, and the right-hand side is
--   closed and convex, the smallest closed convex set containing $S_1 \cap S_2$ is contained in it too.
--   Applied at each step of the hull-relaxation hierarchy, this shows that intersecting two conjuncts
--   *before* taking their convex hull (a basic step, followed by hull-relaxation) never produces a
--   *weaker* relaxation than taking the convex hulls first and then intersecting — only a tighter or
--   equal one, which is exactly the monotone-decreasing chain Theorem 4.7 asserts.
--
--   **Formalization Note.** No hypothesis beyond $S_1, S_2$ being unions of (possibly differently
--   shaped) polyhedra; the inclusion direction is the one the book states (not the reverse, which
--   Theorem 4.8 characterizes exactly).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 53, Lemma 4.6

import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

namespace Disjunctive.NormalForms

/-- Lemma 4.6 (Balas §4.2, p. 53): the closed convex hull of an intersection of two unions of
polyhedra sits inside the intersection of their closed convex hulls. -/
theorem convex_hull_intersection_subset {n : ℕ} {Q1 Q2 : Type*} [Fintype Q1] [Fintype Q2]
    (m1 : Q1 → ℕ) (A1 : (i : Q1) → Matrix (Fin (m1 i)) (Fin n) ℝ) (b1 : (i : Q1) → Fin (m1 i) → ℝ)
    (m2 : Q2 → ℕ) (A2 : (i : Q2) → Matrix (Fin (m2 i)) (Fin n) ℝ) (b2 : (i : Q2) → Fin (m2 i) → ℝ) :
    closure (convexHull ℝ
        ((⋃ i : Q1, Poly (A1 i) (b1 i)) ∩ (⋃ i : Q2, Poly (A2 i) (b2 i)))) ⊆
      closure (convexHull ℝ (⋃ i : Q1, Poly (A1 i) (b1 i))) ∩
        closure (convexHull ℝ (⋃ i : Q2, Poly (A2 i) (b2 i))) := by sorry

end Disjunctive.NormalForms
