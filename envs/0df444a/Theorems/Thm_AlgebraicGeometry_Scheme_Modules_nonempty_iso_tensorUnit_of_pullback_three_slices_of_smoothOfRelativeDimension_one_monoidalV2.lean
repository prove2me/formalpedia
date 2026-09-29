-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices_of_smoothOfRelativeDimension_one_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices_of_smoothOfRelativeDimension_one_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/0dcacc42-c245-55cd-9927-ec90c3d01204
-- title:
--   Theorem of the cube with a curve factor
-- statement:
--   Let $k$ be an algebraically closed field and let $C$, $Y$, $Z$ be objects of the category of schemes over $\operatorname{Spec} k$, with the cartesian monoidal structure on that category (so $C \otimes Y \otimes Z$ has underlying scheme the fibre product $C \times_k Y \times_k Z$, and the monoidal unit is $\operatorname{Spec} k$ over itself). Assume the structure morphism of $C$ is proper and smooth of relative dimension $1$ and that $C$ has integral underlying scheme; that the structure morphism of $Y$ is proper with $Y$ integral; and that the structure morphism of $Z$ is locally of finite type with $Z$ integral. Let $c_0, y_0, z_0$ be morphisms from the monoidal unit to $C$, $Y$, $Z$ respectively, i.e. $k$-rational points. Let $L$ be a sheaf of modules on the scheme underlying $C \otimes Y \otimes Z$ which is invertible in the sense that every point has an open neighbourhood $U$ on which the pullback of $L$ along the inclusion $U \hookrightarrow C \times_k Y \times_k Z$ admits an isomorphism to the unit sheaf of modules of $U$. Assume that the pullbacks of $L$ along the three slice sections $Y \otimes Z \to C \otimes Y \otimes Z$ given by $(c_0, \mathrm{id})$, $C \otimes Z \to C \otimes Y \otimes Z$ given by $(\mathrm{pr}_C, y_0, \mathrm{pr}_Z)$, and $C \otimes Y \to C \otimes Y \otimes Z$ given by $(\mathrm{pr}_C, \mathrm{pr}_Y, z_0)$ each admit an isomorphism to the unit object, i.e. to the structure sheaf of the respective slice. Then $L$ admits an isomorphism to the unit object, i.e. $L$ is trivial.
--
--   This is the theorem of the cube in the case where the first proper factor is a smooth curve — the case to which Mumford's argument reduces the general statement and then treats directly. It is cited by the corresponding general statement [`AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices_monoidalV2`](thm.html#AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices_monoidalV2), which in turn underlies the construction and basic properties of Picard schemes and Néron models used later in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices_of_smoothOfRelativeDimension_one_monoidalV2.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CartesianMonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices_of_smoothOfRelativeDimension_one_monoidalV2
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
