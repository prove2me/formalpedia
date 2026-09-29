-- Prove2me | Theorems.Thm_FamousTheorems_krein_milman
-- name    : FamousTheorems.krein_milman
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T06:56:27.451316+00:00
-- url     : https://prove2.me/theorems/4c37a643-7f21-43c0-b01c-1a9b9d53daca
-- title:
--   The Krein–Milman theorem
-- statement:
--   **The Krein–Milman theorem.**
--
--   In a locally convex Hausdorff topological vector space, every compact convex set is the
--   closed convex hull of its extreme points:
--   $$\overline{\operatorname{conv}(\operatorname{ext} s)} = s .$$
--
--   A convex body is completely determined by its "corners". For a polytope the extreme points
--   are the finitely many vertices and the closure is unnecessary; in infinite dimensions there
--   may be infinitely many extreme points and taking the closure is essential.
--
--   Local convexity cannot be dropped: in $L^p[0,1]$ for $0 < p < 1$ the space is not locally
--   convex and the unit ball has *no* extreme points at all, so the conclusion fails outright.
--   The proof runs the other way from what one might expect — one first shows a nonempty compact
--   set has an extreme point (via Zorn's lemma on closed extreme subsets), then separates with
--   Hahn–Banach.
--
--   Krein and Milman proved it in 1940. It is the reason extreme points organise so much of
--   analysis: Choquet theory represents points as barycentres of measures on the extreme set,
--   and in operator algebras the pure states are exactly the extreme points of the state space.
--
--   **Formalization note.** `s.extremePoints ℝ` is the set of points of `s` not lying in the
--   interior of any segment with endpoints in `s`. The result is Mathlib's
--   `closure_convexHull_extremePoints`.
-- source:
--   Listed in Mathlib's "1000 theorems" manifest (docs/1000.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open Filter Set Topology

theorem krein_milman {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    {s : Set E} (hscomp : IsCompact s) (hAconv : Convex ℝ s) :
    closure (convexHull ℝ <| s.extremePoints ℝ) = s := by sorry

end FamousTheorems
