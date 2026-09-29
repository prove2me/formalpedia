-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/56ce3454-d366-5e45-885d-1c4df03f6bbc
-- title:
--   Theorem of the cube over an algebraically closed field
-- statement:
--   Let $k$ be an algebraically closed field and let $X$, $Y$, $Z$ be objects of the category of schemes over $\mathrm{Spec}\,k$, so each is a scheme `·.left` together with a structure morphism `·.hom` to $\mathrm{Spec}\,k$; assume that $X$ and $Y$ have proper structure morphism and integral underlying scheme, and that $Z$ has separated, locally of finite type and quasi-compact structure morphism and integral underlying scheme. Let $x_0$, $y_0$, $z_0$ be morphisms over $\mathrm{Spec}\,k$ from the monoidal unit (the terminal object $\mathrm{Spec}\,k$) to $X$, $Y$, $Z$ respectively, i.e. $k$-points. Let $L$ be an object of the category of sheaves of modules on the scheme underlying $X \otimes Y \otimes Z$, the triple fibre product over $\mathrm{Spec}\,k$, and assume $L$ is invertible in the sense that every point of that scheme has an open neighbourhood $U$ with the pullback of $L$ along the inclusion $U \hookrightarrow X \otimes Y \otimes Z$ isomorphic to the unit sheaf of modules on $U$. Assume the three slice inclusions, namely $\langle x_0 \circ {!}, \mathrm{id}\rangle : Y \otimes Z \to X \otimes Y \otimes Z$, $\langle \mathrm{pr}_X, \langle y_0 \circ {!}, \mathrm{pr}_Z\rangle\rangle : X \otimes Z \to X \otimes Y \otimes Z$ and $\langle \mathrm{pr}_X, \langle \mathrm{pr}_Y, z_0 \circ {!}\rangle\rangle : X \otimes Y \to X \otimes Y \otimes Z$, each pull $L$ back to a sheaf of modules admitting an isomorphism to the monoidal unit. Then there exists an isomorphism from $L$ to the monoidal unit. All isomorphism assumptions and the conclusion are stated as nonemptiness of the type of isomorphisms.
--
--   This is the theorem of the cube: a line bundle on a product $X \times Y \times Z$ of $k$-varieties, with $X$ and $Y$ complete, which is trivial on the three slices through a chosen rational point is trivial. It is used in the construction of the theorem-of-the-cube identities for line bundles on abelian varieties, in particular in [`AlgebraicGeometry.Scheme.Modules.nonempty_pullback_mul_mul_tensor_iso_monoidalV2`](thm.html#AlgebraicGeometry.Scheme.Modules.nonempty_pullback_mul_mul_tensor_iso_monoidalV2) and in the treatment of polarisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices_monoidalV2.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CartesianMonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices_monoidalV2
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
