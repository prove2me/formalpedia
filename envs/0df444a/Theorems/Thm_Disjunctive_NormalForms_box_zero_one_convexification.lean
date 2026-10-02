-- Prove2me | Theorems.Thm_Disjunctive_NormalForms_box_zero_one_convexification
-- name    : Disjunctive.NormalForms.box_zero_one_convexification
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:30:16.885741+00:00
-- url     : https://prove2.me/theorems/127c79db-11fe-491a-9c9b-4ffb54a8a6f7
-- title:
--   Corollary 4.9 — 0-1 basic steps bring no gain
-- statement:
--   This is Corollary 4.9 of Balas's *Disjunctive Programming*, an immediate consequence of
--   Theorem 4.8 for the most common disjunctions in integer programming.
--
--   Let $K := \{x \in \mathbb{R}^n : 0 \le x_j \le 1,\ j=1,\dots,n\}$ and, for each $j$, let
--   $S_j := K \cap \{x_j \le 0 \lor x_j \ge 1\}$. Then
--
--   $$
--   \mathrm{conv}\Big(\bigcap_{j=1}^n S_j\Big) = \bigcap_{j=1}^n \mathrm{conv}(S_j).
--   $$
--
--   So basic steps that merge several "0-1" disjunctions $x_j \le 0 \lor x_j \ge 1$ *before* taking
--   the hull-relaxation bring no gain over taking each one's convex hull separately: the
--   hull-relaxation of the merged disjunction equals the intersection of the individual ones. To
--   obtain a strictly tighter relaxation via a basic step, the disjunctions merged must involve some
--   other constraint, not merely more 0-1 disjunctions among themselves.
--
--   **Formalization Note.** Stated directly for `K` and `S_j` as displayed, with no additional
--   definitions needed beyond those already introduced for the chapter.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 53, Corollary 4.9

import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

namespace Disjunctive.NormalForms

/-- Corollary 4.9 (Balas §4.3, p. 55): for the unit box `K` and the "0-1" disjunctions
`S_j := K ∩ {x_j ≤ 0 ∨ x_j ≥ 1}`, taking the convex hull before or after intersecting all `n`
disjunctions gives the same result. -/
theorem box_zero_one_convexification {n : ℕ} :
    closure (convexHull ℝ
        (⋂ j : Fin n, {x : Fin n → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1)} ∩
          ({x : Fin n → ℝ | x j ≤ 0} ∪ {x : Fin n → ℝ | 1 ≤ x j}))) =
      ⋂ j : Fin n, closure (convexHull ℝ
        ({x : Fin n → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1)} ∩
          ({x : Fin n → ℝ | x j ≤ 0} ∪ {x : Fin n → ℝ | 1 ≤ x j}))) := by sorry

end Disjunctive.NormalForms
