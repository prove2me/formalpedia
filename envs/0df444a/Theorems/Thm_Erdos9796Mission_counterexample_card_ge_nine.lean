-- Prove2me | Theorems.Thm_Erdos9796Mission_counterexample_card_ge_nine
-- name    : Erdos9796Mission.counterexample_card_ge_nine
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-05T22:50:07.167724+00:00
-- url     : https://prove2.me/theorems/c35e1c76-5531-4585-9ced-8c47a929793e
-- title:
--   Counting obstruction: a counterexample has at least nine vertices
-- statement:
--   Every nonempty convex-independent finite planar set with the 4-equidistant property has cardinality at least nine. The formalization follows Dumitrescu's 2006 isosceles-count route, with cap-witness refinements associated in the source with Nivasch–Pach–Pinchasi–Zerbib (2013). These citations record mathematical provenance only; the Lean declaration and proof are this project's own formalization and do not import or directly machine-check a paper proof.
-- source:
--   Adrian Dumitrescu, On Distinct Distances from a Vertex of a Convex Polygon, Discrete & Computational Geometry 36 (2006), 503–509, DOI 10.1007/s00454-006-1262-y; Gabriel Nivasch, János Pach, Rom Pinchasi, and Shira Zerbib, The Number of Distinct Distances from a Vertex of a Convex Polygon, Journal of Computational Geometry 4 (2013), 1–12, arXiv:1207.1266
--   Source snapshot: https://github.com/mysticflounder/erdos-97-96-formalization/blob/14bcb9baa1b2ce2dd563e5a43527a30b7582483f/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Erdos9796Mission_counterexample_card_ge_nine.lean#L1-L11

/- Statement-only mission draft: SKETCH — NOT PROMOTABLE.
Source and precise status are recorded in items.json. -/
import Definitions.Def_Erdos9796Mission
open Erdos9796Mission

theorem Erdos9796Mission.counterexample_card_ge_nine :
    ∀ A : Finset Plane, A.Nonempty → ConvexIndep (A : Set Plane) → HasNEquidistantProperty 4 A → 9 ≤ A.card := by sorry
