-- Prove2me | Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact
-- name    : AlgebraicGeometry.LocallyQuasiFinite.descendsAlong_surjective_inf_flat_inf_quasiCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/adb03d65-fc5d-57cd-912f-b34d955393b2
-- title:
--   Locally quasi-finite morphisms descend along faithfully flat quasi-compact base change
-- statement:
--   The assertion is the single proposition `DescendsAlong (@LocallyQuasiFinite) (@Surjective ⊓ @Flat ⊓ @QuasiCompact)` for morphism properties of schemes in a fixed universe $u$. Here `⊓` is the pointwise intersection of morphism properties, so the second class consists of those morphisms of schemes that are simultaneously surjective, flat and quasi-compact. Unwinding Mathlib's `DescendsAlong`: for every cartesian square of schemes
--   $$\begin{array}{ccc} X' & \longrightarrow & X\\ \downarrow & & \downarrow f\\ Y' & \xrightarrow{\,g\,} & Y \end{array}$$
--   in which the base-change morphism $g \colon Y' \to Y$ is surjective, flat and quasi-compact, if the pulled-back morphism $X' \to Y'$ is locally quasi-finite then so is $f \colon X \to Y$. No further hypotheses are imposed on $X$, $Y$, $Y'$ or on $f$ itself; in particular neither $f$ nor $g$ is assumed locally of finite type or separated beyond what is contained in the stated properties. The converse direction (stability of locally quasi-finite morphisms under base change) is not part of this statement.
--
--   This is fpqc descent for the property of being locally quasi-finite (Stacks Project tag 02KZ; EGA IV, 2.7.1), in the form packaged by Mathlib's `DescendsAlong` so that it can be applied to a cartesian square through the generic transfer lemmas. It is used here to deduce quasi-finiteness at a point of a morphism from quasi-finiteness of a faithfully flat quasi-compact base change, in [`AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_of_isPullback_of_locallyQuasiFinite`](thm.html#AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_of_isPullback_of_locallyQuasiFinite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_LocallyQuasiFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MorphismProperty AlgebraicGeometry

theorem AlgebraicGeometry.LocallyQuasiFinite.descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong (@LocallyQuasiFinite : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by sorry
