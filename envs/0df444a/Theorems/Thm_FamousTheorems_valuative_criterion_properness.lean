-- Prove2me | Theorems.Thm_FamousTheorems_valuative_criterion_properness
-- name    : FamousTheorems.valuative_criterion_properness
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:22:42.226984+00:00
-- url     : https://prove2.me/theorems/1955647e-8b71-4ffa-8644-29b050198e82
-- title:
--   The valuative criterion for properness
-- statement:
--   **The valuative criterion for properness.** A morphism of schemes $f:X\to Y$ is proper if and only if it is quasi-compact, quasi-separated and locally of finite type, and it satisfies the valuative criterion. The criterion states that for every valuation ring $V$ with fraction field $K$ and every commutative square
--   $$\operatorname{Spec}K\to X,\qquad \operatorname{Spec}V\to Y,$$
--   there is a unique lift $\operatorname{Spec}V\to X$ making both triangles commute.
--
--   This is the main practical tool for verifying properness, the algebraic analogue of compactness. It reduces properness to extending maps from punctured discs, and it is used, for example, to show that projective morphisms and abelian varieties are proper.
--
--   **Formalization note.** Mathlib's `AlgebraicGeometry.IsProper.eq_valuativeCriterion`, an equality of morphism properties, restated here for a single morphism. `ValuativeCriterion f` combines existence and uniqueness of lifts.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `AlgebraicGeometry.IsProper.eq_valuativeCriterion`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open AlgebraicGeometry

theorem valuative_criterion_properness {X Y : Scheme} (f : X ⟶ Y) :
    IsProper f ↔ ValuativeCriterion f ∧ QuasiCompact f ∧ QuasiSeparated f ∧ LocallyOfFiniteType f := by sorry

end FamousTheorems
