-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_tensor_of_pullback_baseChangeSnd_iso_of_tensor_iso_unit
-- name    : AlgebraicGeometry.RelPicard.isAlgEquivZero_tensor_of_pullback_baseChangeSnd_iso_of_tensor_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/d0e7c923-db36-52a5-b1e4-e55de952cb4e
-- title:
--   Algebraic equivalence of two fibres of an invertible family
-- statement:
--   Let $k$ and $K$ be fields and let $\kappa\colon\operatorname{Spec}K\to\operatorname{Spec}k$ be a morphism of affine schemes. Let $x\colon X\to\operatorname{Spec}k$ and $hV\colon V\to\operatorname{Spec}K$ be morphisms of schemes, with $hV$ locally of finite type and geometrically integral, and regard $V$ as a $k$-scheme via $hV$ followed by $\kappa$. Let $F$ be a module on the fibre product $X\times_{\operatorname{Spec}k}V$ (the pullback of $x$ along $hV\circ\kappa$) which is invertible, in the sense that every point has an open neighbourhood $U$ over which the restriction of $F$ along $U\hookrightarrow X\times_k V$ is isomorphic to the unit module. Let $v_0,v_1\colon\operatorname{Spec}K\to V$ be sections of $hV$. Let $A$, $B$, $P$ be modules on $X_K:=X\times_{\operatorname{Spec}k}\operatorname{Spec}K$ (the pullback of $x$ along $\kappa$), with isomorphisms $eA$ and $eB$ identifying $A$ and $B$ with the pullbacks of $F$ along the base-change maps $X_K\to X\times_kV$ induced by $v_0$ and by $v_1$ respectively (each being a morphism over $\operatorname{Spec}k$ from $\kappa$ to $hV\circ\kappa$), with $P$ invertible in the same local sense, and with an isomorphism $A\otimes P\cong\mathbf 1$ onto the unit module of $X_K$. Then $B\otimes P$ satisfies `IsAlgEquivZero` for the structure morphism $\operatorname{pr}_2\colon X_K\to\operatorname{Spec}K$: there are a scheme $T'$ and a morphism $h\colon T'\to\operatorname{Spec}K$ that is locally of finite type and geometrically integral, an invertible module $M$ on $X_K\times_{\operatorname{Spec}K}T'$, and two sections $t_0,t_1$ of $h$, such that the pullback of $M$ along the base change induced by $t_0$ is isomorphic to the unit module on $X_K\times_{\operatorname{Spec}K}\operatorname{Spec}K$, while the pullback of $M$ along the base change induced by $t_1$ is isomorphic to the pullback of $B\otimes P$ along the first projection.
--
--   This is the statement that two fibres of a single family of invertible modules over a geometrically integral parameter scheme differ, after twisting by an invertible module trivialising one of them, by a module algebraically equivalent to zero in the one-step sense used in this development; the mixed setting has the ambient scheme $X$ defined over $k$ and the parameter scheme $V$ over $K$. It is used in the construction of one-step algebraic-equivalence witnesses after a change of curve, in [`AlgebraicGeometry.RelPicard.exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves`](thm.html#AlgebraicGeometry.RelPicard.exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_tensor_of_pullback_baseChangeSnd_iso_of_tensor_iso_unit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.isAlgEquivZero_tensor_of_pullback_baseChangeSnd_iso_of_tensor_iso_unit
    {k : Type u} [Field k] {K : Type u} [Field K] (κ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    {X V : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (hV : V ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType hV] [GeometricallyIntegral hV]
    (F : (pullback x (hV ≫ κ)).Modules) (hF : Scheme.Modules.IsInvertible F)
    (v₀ v₁ : Spec (CommRingCat.of K) ⟶ V) (hv₀ : v₀ ≫ hV = 𝟙 _) (hv₁ : v₁ ≫ hV = 𝟙 _)
    (A B P : (pullback x κ).Modules)
    (eA : (Scheme.Modules.pullback (baseChangeSnd x
      (⟨v₀, by rw [← Category.assoc, hv₀, Category.id_comp]⟩ : SchemeHomOver κ (hV ≫ κ)))).obj F ≅ A)
    (eB : (Scheme.Modules.pullback (baseChangeSnd x
      (⟨v₁, by rw [← Category.assoc, hv₁, Category.id_comp]⟩ : SchemeHomOver κ (hV ≫ κ)))).obj F ≅ B)
    (hP : Scheme.Modules.IsInvertible P) (eP : A ⊗ P ≅ 𝟙_ (pullback x κ).Modules) :
    IsAlgEquivZero (pullback.snd x κ) (B ⊗ P) := by sorry
