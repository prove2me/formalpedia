-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact
-- name    : AlgebraicGeometry.IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasiCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/d3ab390d-965d-5152-9d6f-430711fd4e94
-- title:
--   Affineness of morphisms descends along faithfully flat quasi-compact maps
-- statement:
--   The statement is a single closed assertion about morphism properties of schemes in a fixed universe $u$, with no variables or hypotheses of its own. It asserts `DescendsAlong` for the property `IsAffineHom` of being an affine morphism relative to the class $\mathrm{Surjective} \sqcap \mathrm{Flat} \sqcap \mathrm{QuasiCompact}$, the infimum in the lattice of morphism properties of schemes, i.e. the class of morphisms that are simultaneously surjective, flat and quasi-compact. Unfolding the descent predicate: whenever a square of schemes is cartesian, with one side a morphism $g$ that is surjective, flat and quasi-compact, and the opposite side a morphism $f$ whose base change along $g$ is an affine morphism, then $f$ itself is an affine morphism. Thus affineness of a morphism is a property that may be tested after an fpqc base change of the stated kind (surjectivity, flatness and quasi-compactness of the covering morphism, with no finiteness or local-finite-presentation assumption).
--
--   This is fpqc descent for affine morphisms (SGA 1, Exposé VIII, Corollaire 5.6; EGA IV, 2.7.1). It is used in the construction of fake elliptic curves in the Čerednik–Drinfeld part of the development and in establishing good reduction properties of the relative group law on Jacobians, in both cases to recognise affineness of a morphism after passage to a flat cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MorphismProperty AlgebraicGeometry

theorem AlgebraicGeometry.IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong (@IsAffineHom : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by sorry
