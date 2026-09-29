-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/98274c82-cd08-5a21-a017-2f343612639c
-- title:
--   Invertible modules on the spectrum of a field are trivial
-- statement:
--   Let $k$ be a field and let $L$ be an object of the category $(\operatorname{Spec} k)$`.Modules` of sheaves of modules over the sheaf of rings of the scheme $\operatorname{Spec}(\mathrm{CommRingCat.of}\ k)$. Assume that $L$ satisfies `Scheme.Modules.IsInvertible`, that is: for every point $x$ of $\operatorname{Spec} k$ there exist an open subscheme $U$ of $\operatorname{Spec} k$ with $x \in U$ and an isomorphism, in the category of sheaves of modules on $U$, between the pullback of $L$ along the open immersion $U \hookrightarrow \operatorname{Spec} k$ and the unit object `SheafOfModules.unit` of the ring sheaf of $U$ (the structure sheaf of $U$ viewed as a module over itself). The conclusion is that the type of isomorphisms $L \cong \mathbb{1}$ is nonempty, where $\mathbb{1}$ is the monoidal unit of $(\operatorname{Spec} k)$`.Modules`; that is, $L$ is isomorphic to the structure sheaf of $\operatorname{Spec} k$ as a module over itself. No constructive choice of isomorphism is made: only its existence is asserted.
--
--   This is the statement $\operatorname{Pic}(\operatorname{Spec} k) = 0$ for a field $k$, in the form needed for sheaves of modules on schemes. It is used throughout the treatment of relative Picard functors and rigidified line bundles, where twists by a line bundle pulled back from a curve over $k$ are shown to disappear after restriction along a section over the base field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field
    (k : Type u) [Field k] (L : (Spec (CommRingCat.of k)).Modules) (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (L ≅ 𝟙_ (Spec (CommRingCat.of k)).Modules) := by sorry
