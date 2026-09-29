-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_rigidified_locIsoOnBase_of_section
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_rigidified_locIsoOnBase_of_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/7d367171-30ca-5ede-8847-18a5cd466328
-- title:
--   Rigidifying an invertible module along a section, locally on the base
-- statement:
--   Let $T$ be a commutative ring, let $B$ be a scheme, let $h \colon B \to \operatorname{Spec} T$ be a morphism of schemes and let $e \colon \operatorname{Spec} T \to B$ be a section of $h$, in the sense that $e$ followed by $h$ is the identity of $\operatorname{Spec} T$. Let $M$ be an object of the category of modules on $B$ which is invertible in the sense of the project predicate `Scheme.Modules.IsInvertible`: for every point $x$ of $B$ there is an open $U \subseteq B$ containing $x$ such that the pullback of $M$ along the inclusion $U \hookrightarrow B$ is isomorphic to the unit module on $U$. The assertion is that there exists a module $M_1$ on $B$ with the following three properties: $M_1$ is invertible in the same sense; the pullback $e^{*}M_1$ admits an isomorphism to the unit module on $\operatorname{Spec} T$ (the set of such isomorphisms is asserted to be nonempty, no isomorphism being chosen); and `LocIsoOnBase h M M₁` holds, i.e. for every point $s$ of $\operatorname{Spec} T$ there is an open $U \subseteq \operatorname{Spec} T$ containing $s$ such that the pullbacks of $M$ and of $M_1$ along the inclusion $h^{-1}U \hookrightarrow B$ are isomorphic.
--
--   This is the standard rigidification twist used in the construction of the relative Picard functor: an invertible module on a scheme over $\operatorname{Spec} T$ carrying a section can be altered by the pullback of an invertible module on the base so as to become trivial along the section, without changing its isomorphism class locally on the base. It feeds the treatment of rigidified line bundles and is used in [`AlgebraicGeometry.Polarisation.exists_isInvertible_locIsoOnBase_pullback_of_locIsoOnBase_of_faithfullyFlat_of_section`](thm.html#AlgebraicGeometry.Polarisation.exists_isInvertible_locIsoOnBase_pullback_of_locIsoOnBase_of_faithfullyFlat_of_section).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_rigidified_locIsoOnBase_of_section.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_rigidified_locIsoOnBase_of_section
    {T : Type u} [CommRing T] {B : Scheme.{u}} (h : B ⟶ Spec (CommRingCat.of T))
    (e : Spec (CommRingCat.of T) ⟶ B) (he : e ≫ h = 𝟙 _)
    (M : B.Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ M₁ : B.Modules, Scheme.Modules.IsInvertible M₁ ∧
      Nonempty ((Scheme.Modules.pullback e).obj M₁ ≅ SheafOfModules.unit (Spec (CommRingCat.of T)).ringCatSheaf) ∧
      LocIsoOnBase h M M₁ := by sorry
