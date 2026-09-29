-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact
-- name    : AlgebraicGeometry.IsSeparated.descendsAlong_surjective_inf_flat_inf_quasiCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/bd2d4bb6-3b79-5359-9880-cadfce8f9f9d
-- title:
--   Separatedness descends along faithfully flat quasi-compact morphisms
-- statement:
--   The assertion is that the morphism property `IsSeparated` on the category of schemes (in a fixed universe $u$) descends along the property $\text{Surjective} \sqcap \text{Flat} \sqcap \text{QuasiCompact}$, i.e. along surjective flat quasi-compact morphisms. Unwinding Mathlib's `DescendsAlong`: for all schemes $X, S', S$ and morphisms $f : X \to S$ and $g : S' \to S$ admitting a pullback, if $g$ is surjective, flat and quasi-compact, and if the base change $X \times_S S' \to S'$ of $f$ along $g$ is separated (its diagonal is a closed immersion), then $f$ itself is separated. Equivalently, in a cartesian square with horizontal maps $X \times_S S' \to X$ and $g : S' \to S$ and vertical maps the base change $f'$ and $f$, separatedness of $f'$ together with the assumption that $g$ is faithfully flat and quasi-compact forces separatedness of $f$. The statement is registered as an instance-style fact about morphism properties, with no finiteness or separatedness hypothesis on $g$ beyond quasi-compactness.
--
--   This is the fpqc descent statement for separatedness (EGA IV 2.7.1). It is used to obtain the corresponding descent statement for properness, [`AlgebraicGeometry.IsProper.descendsAlong_surjective_inf_flat_inf_quasiCompact`](thm.html#AlgebraicGeometry.IsProper.descendsAlong_surjective_inf_flat_inf_quasiCompact), and in the Néron model infrastructure, where a relative group law on a scheme is produced from descent data along a finite étale covering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MorphismProperty AlgebraicGeometry

theorem AlgebraicGeometry.IsSeparated.descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by sorry
