-- Prove2me | Theorems.Thm_AlgebraicGeometry_LocallyOfFiniteType_descendsAlong_surjective_inf_flat_inf_quasiCompact
-- name    : AlgebraicGeometry.LocallyOfFiniteType.descendsAlong_surjective_inf_flat_inf_quasiCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/a1f7c14a-d3de-5fba-95dc-84f8ed6d0791
-- title:
--   Locally of finite type descends along fpqc morphisms
-- statement:
--   For schemes in a fixed universe, the morphism property `LocallyOfFiniteType` descends along the morphism property obtained as the pointwise intersection $\mathtt{Surjective} \sqcap \mathtt{Flat} \sqcap \mathtt{QuasiCompact}$, that is, along morphisms that are simultaneously surjective, flat and quasi-compact (fpqc morphisms). Unfolding Mathlib's `DescendsAlong`: given a cartesian square of schemes with bottom edge $g : S' \to S$ and right edge $f : X \to S$, whose remaining edges exhibit the top-left corner as a pullback, if $g$ is surjective, flat and quasi-compact, and if the base change $f' : X \times_S S' \to S'$ of $f$ along $g$ is locally of finite type, then $f$ itself is locally of finite type. No finiteness or separatedness assumption is placed on $f$ or on the schemes involved, and the conclusion is the full descent statement for arbitrary such squares, not merely for a fixed covering family.
--
--   This is the fpqc descent of the property of being locally of finite type (EGA IV 2.7.1): the property is local on the base for the fpqc topology. It is used to obtain the corresponding descent statement for proper morphisms, [`AlgebraicGeometry.IsProper.descendsAlong_surjective_inf_flat_inf_quasiCompact`](thm.html#AlgebraicGeometry.IsProper.descendsAlong_surjective_inf_flat_inf_quasiCompact), and more generally feeds the pullback-and-descend machinery for morphism properties.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_LocallyOfFiniteType_descendsAlong_surjective_inf_flat_inf_quasiCompact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MorphismProperty AlgebraicGeometry

theorem AlgebraicGeometry.LocallyOfFiniteType.descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by sorry
