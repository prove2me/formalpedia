-- Prove2me | Theorems.Thm_Disjunctive_NormalForms_convex_hull_intersection_eq_iff
-- name    : Disjunctive.NormalForms.convex_hull_intersection_eq_iff
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:29:50.306983+00:00
-- url     : https://prove2.me/theorems/b7ab7537-298d-4d56-9872-54e68df8d9ba
-- title:
--   Theorem 4.8 — when convexifying before or after an intersection agree
-- statement:
--   This is Theorem 4.8 of Balas's *Disjunctive Programming*, sharpening Lemma 4.6 into an exact
--   criterion for when a basic step's hull-relaxation gain is real.
--
--   For unions of polyhedra $S_1 = \bigcup_{i \in Q_1} P_i$, $S_2 = \bigcup_{k \in Q_2} P_k$:
--
--   $$
--   \mathrm{cl}\,\mathrm{conv}(S_1 \cap S_2) = (\mathrm{cl}\,\mathrm{conv}\,S_1) \cap
--   (\mathrm{cl}\,\mathrm{conv}\,S_2)
--   $$
--
--   if and only if every extreme point and every extreme direction vector of the right-hand side is
--   already an extreme point (resp. direction) of some single pair's intersection $P_i \cap P_k$,
--   $(i,k) \in Q_1 \times Q_2$. When this fails, taking the convex hull *before* intersecting is
--   strictly weaker than taking it *after* — telling a practitioner exactly when a basic step
--   followed by hull-relaxation is worth its added variables, and when it produces no gain at all.
--
--   **Formalization Note.** `ExtremeDirections` is the companion definition (extreme rays of the
--   recession cone); the two existential conditions (for extreme points and for extreme directions)
--   mirror the book's own "extreme point (extreme direction)" parenthetical exactly, stated as a
--   conjunction of two separate universally-quantified conditions rather than folded into one.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 53, Theorem 4.8

import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

namespace Disjunctive.NormalForms

/-- Theorem 4.8 (Balas §4.3, p. 53-54): equality in Lemma 4.6 holds exactly when every extreme
point and every extreme direction of the intersection of the two closed convex hulls already
comes from a single pair of polyhedra `P_i ∩ P_k`. -/
theorem convex_hull_intersection_eq_iff {n : ℕ} {Q1 Q2 : Type*} [Fintype Q1] [Fintype Q2]
    (m1 : Q1 → ℕ) (A1 : (i : Q1) → Matrix (Fin (m1 i)) (Fin n) ℝ) (b1 : (i : Q1) → Fin (m1 i) → ℝ)
    (m2 : Q2 → ℕ) (A2 : (i : Q2) → Matrix (Fin (m2 i)) (Fin n) ℝ) (b2 : (i : Q2) → Fin (m2 i) → ℝ) :
    closure (convexHull ℝ
          ((⋃ i : Q1, Poly (A1 i) (b1 i)) ∩ (⋃ i : Q2, Poly (A2 i) (b2 i)))) =
        closure (convexHull ℝ (⋃ i : Q1, Poly (A1 i) (b1 i))) ∩
          closure (convexHull ℝ (⋃ i : Q2, Poly (A2 i) (b2 i))) ↔
      (∀ x ∈ Set.extremePoints ℝ
            (closure (convexHull ℝ (⋃ i : Q1, Poly (A1 i) (b1 i))) ∩
              closure (convexHull ℝ (⋃ i : Q2, Poly (A2 i) (b2 i)))),
          ∃ i k, x ∈ Set.extremePoints ℝ (Poly (A1 i) (b1 i) ∩ Poly (A2 k) (b2 k))) ∧
        (∀ y ∈ ExtremeDirections
              (closure (convexHull ℝ (⋃ i : Q1, Poly (A1 i) (b1 i))) ∩
                closure (convexHull ℝ (⋃ i : Q2, Poly (A2 i) (b2 i)))),
            ∃ i k, y ∈ ExtremeDirections (Poly (A1 i) (b1 i) ∩ Poly (A2 k) (b2 k))) := by sorry

end Disjunctive.NormalForms
