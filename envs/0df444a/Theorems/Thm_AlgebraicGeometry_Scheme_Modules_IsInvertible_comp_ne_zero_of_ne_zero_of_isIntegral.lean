-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comp_ne_zero_of_ne_zero_of_isIntegral
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.comp_ne_zero_of_ne_zero_of_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/f4f16287-6bac-51b8-8998-5886a9454a6e
-- title:
--   Non-zero sections compose non-trivially on an integral scheme
-- statement:
--   Let $X$ be an integral scheme and let $M$ be a module over $X$ (an object of `X.Modules`), assumed invertible in the sense of the project predicate `Scheme.Modules.IsInvertible`: for every point $x$ of $X$ there is an open $U \subseteq X$ with $x \in U$ such that the pullback of $M$ along the open immersion $U.\iota$ is isomorphic to the unit module $\mathcal{O}_U$ on $U$. Let $s : \mathbb{1} \to M$ and $t : M \to \mathbb{1}$ be morphisms of modules over $X$, where $\mathbb{1} = \mathbb{1}_{X.\mathrm{Modules}}$ denotes the monoidal unit, i.e. the structure sheaf regarded as a module over itself. Assume $s \neq 0$ and $t \neq 0$. Then the composite $s \ggg t$, taken in diagrammatic order ($s$ followed by $t$, that is $t \circ s$), is non-zero as an endomorphism of $\mathbb{1}$. No affineness, quasi-compactness or coherence hypothesis beyond integrality of $X$ and local triviality of $M$ is assumed.
--
--   This is the standard fact that on an integral scheme the pairing between a line bundle and its dual is non-degenerate on non-zero sections, $\operatorname{End}(\mathcal{O}_X)$ being a domain. It is used in the study of rigidified line bundles on abelian schemes and their relative Picard functor, where it supports [`GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_unit_of_ne_zero_section_dual`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_unit_of_ne_zero_section_dual), the statement that a line bundle admitting a non-zero section with non-zero dual section is trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comp_ne_zero_of_ne_zero_of_isIntegral.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.comp_ne_zero_of_ne_zero_of_isIntegral
    {X : Scheme.{u}} [IsIntegral X] {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M) (t : M ⟶ 𝟙_ X.Modules) (hs : s ≠ 0) (ht : t ≠ 0) : s ≫ t ≠ 0 := by sorry
