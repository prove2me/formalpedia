-- Prove2me | Theorems.Thm_Disjunctive_NormalForms_convex_hull_intersection_eq_iff_v2
-- name    : Disjunctive.NormalForms.convex_hull_intersection_eq_iff_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:10.727084+00:00
-- url     : https://prove2.me/theorems/b0aa45ef-7269-4cbe-abfb-2a83e90444d1
-- title:
--   Theorem 4.8 — when convexifying before or after an intersection agree (pointed case)
-- statement:
--   This is Theorem 4.8 of Balas's *Disjunctive Programming*. Let $S_1 = \bigcup_{i \in Q_1} P_i$ and $S_2 = \bigcup_{k \in Q_2} P_k$ be finite unions of polyhedra and suppose that $K := \mathrm{cl\,conv}\, S_1 \cap \mathrm{cl\,conv}\, S_2$ is pointed (contains no line). Then
--
--   $$\mathrm{cl\,conv}(S_1 \cap S_2) = \mathrm{cl\,conv}\, S_1 \cap \mathrm{cl\,conv}\, S_2$$
--
--   if and only if every extreme point of $K$ is an extreme point of $P_i \cap P_k$ for some $(i,k) \in Q_1 \times Q_2$, and every extreme direction vector of $K$ (extreme ray of its recession cone) is an extreme direction vector of $P_i \cap P_k$ for some $(i,k) \in Q_1 \times Q_2$.
--
--   **Formalization Note.** The retired version omitted the pointedness of $K$: when $K$ contains a line it has neither extreme points nor extreme directions, so the criterion holds vacuously while the equality may fail ($S_1 = \{x_1 \le 0\} \cup \{x_1 \ge 2\}$, $S_2 = \{x_1 = 1\}$). The description of a polyhedron by its extreme points and extreme directions, on which the theorem rests, presupposes pointedness; it is now the explicit hypothesis that $K$ contains no line. (If the book obtains pointedness from a stronger standing assumption, e.g. nonnegative variables, that case is covered.)
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §4.3, p. 53-55, Theorem 4.8

import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

namespace Disjunctive.NormalForms

/-- Theorem 4.8 (Balas, *Disjunctive Programming*, Springer 2018, §4.3, p. 53-55): for unions of
polyhedra `S₁ = ⋃_{i∈Q₁} P_i`, `S₂ = ⋃_{k∈Q₂} P_k` such that
`K := cl conv S₁ ∩ cl conv S₂` is pointed (contains no line), `cl conv (S₁ ∩ S₂) = K` holds if
and only if every extreme point of `K` is an extreme point of `P_i ∩ P_k` for some
`(i,k) ∈ Q₁ × Q₂`, and every extreme direction vector of `K` (extreme ray of its recession cone)
is an extreme direction vector of `P_i ∩ P_k` for some `(i,k)`.
Corrected: the retired version dropped the pointedness of `K` that the extreme-point /
extreme-direction description presupposes; for a `K` containing a line (no extreme points or
directions at all) the right-hand side holds vacuously while the equality can fail. -/
theorem convex_hull_intersection_eq_iff_v2 {n : ℕ} {Q1 Q2 : Type*} [Fintype Q1] [Fintype Q2]
    (m1 : Q1 → ℕ) (A1 : (i : Q1) → Matrix (Fin (m1 i)) (Fin n) ℝ) (b1 : (i : Q1) → Fin (m1 i) → ℝ)
    (m2 : Q2 → ℕ) (A2 : (i : Q2) → Matrix (Fin (m2 i)) (Fin n) ℝ) (b2 : (i : Q2) → Fin (m2 i) → ℝ)
    (hpointed : ¬ ∃ x d : Fin n → ℝ, d ≠ 0 ∧ ∀ t : ℝ, x + t • d ∈
      closure (convexHull ℝ (⋃ i : Q1, Poly (A1 i) (b1 i))) ∩
        closure (convexHull ℝ (⋃ i : Q2, Poly (A2 i) (b2 i)))) :
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
