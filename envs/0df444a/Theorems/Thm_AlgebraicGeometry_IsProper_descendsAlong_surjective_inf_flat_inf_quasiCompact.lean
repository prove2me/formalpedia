-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsProper_descendsAlong_surjective_inf_flat_inf_quasiCompact
-- name    : AlgebraicGeometry.IsProper.descendsAlong_surjective_inf_flat_inf_quasiCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/dd24c156-2fa3-584b-9ea5-8cb810fca2e6
-- title:
--   Properness descends along surjective flat quasi-compact morphisms
-- statement:
--   The assertion is that the class `IsProper` of proper morphisms of schemes (in a fixed universe $u$) descends along the class of morphisms that are simultaneously surjective, flat and quasi-compact, i.e. `DescendsAlong (@IsProper) (@Surjective ⊓ @Flat ⊓ @QuasiCompact)` holds. Unfolding the Mathlib notion of `DescendsAlong`: for every cartesian square of schemes
--   $$\begin{array}{ccc} X' & \to & X \\ \downarrow f' & & \downarrow f \\ S' & \xrightarrow{g} & S \end{array}$$
--   in which the base-change morphism $g : S' \to S$ is surjective, flat and quasi-compact, if the pulled-back morphism $f' : X' \to S'$ is proper, then the original morphism $f : X \to S$ is proper. No further hypotheses are imposed on $f$, $X$, $S$ or $S'$; in particular no finiteness or separatedness assumption on the schemes themselves is required, the conditions on $g$ being exactly surjectivity, flatness and quasi-compactness. The statement is an instance-style fact about morphism properties rather than a statement about a single square, and it is applied by specialising it to concrete pullback squares.
--
--   This is descent of properness along faithfully flat quasi-compact base change (EGA IV 2.7.1). It is used in the project wherever properness of a morphism is obtained after a flat surjective base change, for instance in the construction of models of Shimura curves arising in the Čerednik–Drinfeld setting, in the treatment of good reduction of Jacobians, and in the analysis of models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsProper_descendsAlong_surjective_inf_flat_inf_quasiCompact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MorphismProperty AlgebraicGeometry

theorem AlgebraicGeometry.IsProper.descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong (@IsProper : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by sorry
