-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices_of_smoothOfRelativeDimension_one
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/db501d79-0323-5af5-9320-06537acd3c9a
-- title:
--   Theorem of the cube with a curve factor
-- statement:
--   Let $k$ be an algebraically closed field and let $C$, $Y$, $Z$ be objects of the category of schemes over $\mathrm{Spec}\,k$, with structure morphisms assumed as follows: $C \to \mathrm{Spec}\,k$ is proper and smooth of relative dimension $1$ and $C$ is integral; $Y \to \mathrm{Spec}\,k$ is proper and $Y$ is integral; $Z \to \mathrm{Spec}\,k$ is locally of finite type and $Z$ is integral. Let $c_0$, $y_0$, $z_0$ be morphisms from the monoidal unit $\mathrm{Spec}\,k$ to $C$, $Y$, $Z$ over $\mathrm{Spec}\,k$, that is $k$-rational points. Let $L$ be a sheaf of modules on the scheme underlying $C \otimes Y \otimes Z$ (the triple fibre product over $\mathrm{Spec}\,k$) which is invertible in the sense that every point has an open neighbourhood $U$ on which the pullback of $L$ along $U \hookrightarrow C \otimes Y \otimes Z$ is isomorphic to the unit sheaf of modules on $U$. Assume the pullbacks of $L$ along the three slice sections $(y,z) \mapsto (c_0,y,z)$, $(c,z) \mapsto (c,y_0,z)$ and $(c,y) \mapsto (c,y,z_0)$ each admit an isomorphism with the respective unit sheaf of modules. Then $L$ admits an isomorphism with the unit sheaf of modules on $C \otimes Y \otimes Z$.
--
--   This is the theorem of the cube in the case where the first proper factor is a smooth curve, the case treated directly in Mumford's proof. It is cited by [`AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices`](thm.html#AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices), which removes the curve hypothesis, within the development of relative Picard functors and Néron models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices_of_smoothOfRelativeDimension_one.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CartesianMonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices_of_smoothOfRelativeDimension_one
    (k : Type u) [Field k] [IsAlgClosed k] (C Y Z : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [IsIntegral C.left] [IsProper Y.hom] [IsIntegral Y.left]
    [LocallyOfFiniteType Z.hom] [IsIntegral Z.left]
    (c₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) (y₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Y)
    (z₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Z)
    (L : (C ⊗ Y ⊗ Z).left.Modules) (hL : Scheme.Modules.IsInvertible L)
    (h₁ : Nonempty ((Scheme.Modules.pullback
      (lift (toUnit (Y ⊗ Z) ≫ c₀) (𝟙 (Y ⊗ Z)) : Y ⊗ Z ⟶ C ⊗ Y ⊗ Z).left).obj L ≅ 𝟙_ _))
    (h₂ : Nonempty ((Scheme.Modules.pullback
      (lift (fst C Z) (lift (toUnit (C ⊗ Z) ≫ y₀) (snd C Z)) : C ⊗ Z ⟶ C ⊗ Y ⊗ Z).left).obj L ≅ 𝟙_ _))
    (h₃ : Nonempty ((Scheme.Modules.pullback
      (lift (fst C Y) (lift (snd C Y) (toUnit (C ⊗ Y) ≫ z₀)) : C ⊗ Y ⟶ C ⊗ Y ⊗ Z).left).obj L ≅ 𝟙_ _)) :
    Nonempty (L ≅ 𝟙_ _) := by sorry
