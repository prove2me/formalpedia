-- Prove2me | Theorems.Thm_DoCarmoDG_isoperimetric_inequality
-- name    : DoCarmoDG.isoperimetric_inequality
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:28:31.936912+00:00
-- url     : https://prove2.me/theorems/228d2382-b81f-490e-825e-d7976c85dcee
-- title:
--   Isoperimetric inequality: $l^2 - 4\pi A \ge 0$, with equality only for circles
-- statement:
--   **The isoperimetric inequality** (do Carmo §1-7, Theorem 1, p. 34): let $C$ be a simple closed plane curve of length $l$, and let $A$ be the area of the region bounded by $C$. Then
--
--   $$ l^2 - 4\pi A \ge 0, $$
--
--   and equality holds if and only if $C$ is a circle.
--
--   In the formalization the bounded area is the quantity defined by do Carmo's formula (1); the statement is written with $|A|$ so that it does not presuppose a positively oriented parametrization, and the equality case asserts that the trace of the curve lies on a circle of positive radius.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-7 (pp. 31-46)

import Definitions.Def_DoCarmo_plane_curves

namespace DoCarmoDG

theorem isoperimetric_inequality
    (l : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 2))
    (halpha : IsSimpleClosedCurve l alpha) :
    l ^ 2 - 4 * Real.pi * |signedArea l alpha| ≥ 0 ∧
      (l ^ 2 - 4 * Real.pi * |signedArea l alpha| = 0 ↔
        ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ), 0 < r ∧ ∀ t, ‖alpha t - c‖ = r) := by sorry

end DoCarmoDG
