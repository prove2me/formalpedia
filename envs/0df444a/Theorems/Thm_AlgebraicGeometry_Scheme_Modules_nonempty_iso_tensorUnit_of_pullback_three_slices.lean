-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/59fcde5f-18a9-5d0d-bf32-e82496748fc5
-- title:
--   Theorem of the cube over an algebraically closed field
-- statement:
--   Let $k$ be an algebraically closed field and let $X$, $Y$, $Z$ be objects of the slice category of schemes over $\operatorname{Spec} k$: the structure morphisms of $X$ and $Y$ are proper and their underlying schemes are integral, while the structure morphism of $Z$ is separated, locally of finite type and quasi-compact and its underlying scheme is integral. Let $x_0$, $y_0$, $z_0$ be morphisms from the monoidal unit of the slice category (that is, $\operatorname{Spec} k$ over itself) to $X$, $Y$, $Z$ respectively, i.e. $k$-rational points. Let $L$ be a sheaf of modules on the underlying scheme of the triple product $X \otimes Y \otimes Z$ (the fibre product over $\operatorname{Spec} k$), and assume $L$ satisfies `Scheme.Modules.IsInvertible`: every point of that scheme has an open neighbourhood $U$ such that the pullback of $L$ along the inclusion of $U$ is isomorphic to the unit module sheaf on $U$. Assume further that the pullbacks of $L$ along the three slice inclusions $Y \otimes Z \to X \otimes Y \otimes Z$ given by $x_0$ on the first factor and the identity elsewhere, $X \otimes Z \to X \otimes Y \otimes Z$ given by $y_0$ on the middle factor and the two projections elsewhere, and $X \otimes Y \to X \otimes Y \otimes Z$ given by $z_0$ on the last factor and the two projections elsewhere, each admit an isomorphism to the unit object. Then $L$ admits an isomorphism to the unit object, i.e. $L$ is trivial.
--
--   This is the theorem of the cube: an invertible sheaf on a product of two complete varieties with a third variety, trivial on the three slices through a chosen rational point, is trivial. It is cited by [`AlgebraicGeometry.Scheme.Modules.nonempty_pullback_mul_mul_tensor_iso`](thm.html#AlgebraicGeometry.Scheme.Modules.nonempty_pullback_mul_mul_tensor_iso), the pull-back form of the statement for maps into an abelian variety; the Lean hypotheses on $Z$ spell out separatedness, finite type and quasi-compactness of the structure morphism rather than invoking a single variety predicate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CartesianMonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices
    (k : Type u) [Field k] [IsAlgClosed k] (X Y Z : Over (Spec (CommRingCat.of k)))
    [IsProper X.hom] [IsIntegral X.left] [IsProper Y.hom] [IsIntegral Y.left]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsIntegral Z.left]
    (x₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) (y₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Y)
    (z₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Z)
    (L : (X ⊗ Y ⊗ Z).left.Modules) (hL : Scheme.Modules.IsInvertible L)
    (h₁ : Nonempty ((Scheme.Modules.pullback
      (lift (toUnit (Y ⊗ Z) ≫ x₀) (𝟙 (Y ⊗ Z)) : Y ⊗ Z ⟶ X ⊗ Y ⊗ Z).left).obj L ≅ 𝟙_ _))
    (h₂ : Nonempty ((Scheme.Modules.pullback
      (lift (fst X Z) (lift (toUnit (X ⊗ Z) ≫ y₀) (snd X Z)) : X ⊗ Z ⟶ X ⊗ Y ⊗ Z).left).obj L ≅ 𝟙_ _))
    (h₃ : Nonempty ((Scheme.Modules.pullback
      (lift (fst X Y) (lift (snd X Y) (toUnit (X ⊗ Y) ≫ z₀)) : X ⊗ Y ⟶ X ⊗ Y ⊗ Z).left).obj L ≅ 𝟙_ _)) :
    Nonempty (L ≅ 𝟙_ _) := by sorry
