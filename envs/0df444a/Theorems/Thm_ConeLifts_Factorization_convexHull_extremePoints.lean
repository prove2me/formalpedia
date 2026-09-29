-- Prove2me | Theorems.Thm_ConeLifts_Factorization_convexHull_extremePoints
-- name    : ConeLifts.Factorization.convexHull_extremePoints
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:44:22.859746+00:00
-- url     : https://prove2.me/theorems/5aa18be9-27fc-4c0a-a298-a33e85298252
-- title:
--   §2, p. 3 — a convex body and its polar are the convex hulls of their extreme points
-- statement:
--   Let $C \subseteq \mathbb R^n$ be a convex body: compact, convex, with $0 \in \operatorname{int} C$. Then both $C$ and its polar $C^\circ = \{y : \langle x, y\rangle \le 1\ \forall x \in C\}$ are the convex hulls of their extreme points:
--
--   $$
--   C = \operatorname{conv}(\operatorname{ext} C), \qquad C^\circ = \operatorname{conv}(\operatorname{ext} C^\circ).
--   $$
--
--   This is what lets the slack operator, which only sees extreme points, determine $C$ and $C^\circ$; it is used at the end of both halves of Theorem 2.4.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 3, §2 ("both C and C° are convex hulls of their respective extreme points")

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Shared_polar

namespace ConeLifts.Factorization

/-- Gouveia, Parrilo & Thomas, *Lifts of Convex Sets and Cone Factorizations*,
arXiv:1111.3164v2, §2, p. 3: "Since C is compact with the origin in its interior, both C and C°
are convex hulls of their respective extreme points." -/
theorem convexHull_extremePoints {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsConvexBody C) :
    C = convexHull ℝ (Set.extremePoints ℝ C) ∧
      ConeLifts.Shared.polar C = convexHull ℝ (Set.extremePoints ℝ (ConeLifts.Shared.polar C)) := by sorry

end ConeLifts.Factorization
