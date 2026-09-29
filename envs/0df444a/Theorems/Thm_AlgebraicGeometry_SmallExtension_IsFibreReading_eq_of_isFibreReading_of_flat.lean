-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_IsFibreReading_eq_of_isFibreReading_of_flat
-- name    : AlgebraicGeometry.SmallExtension.IsFibreReading.eq_of_isFibreReading_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/a01cc5cb-b2fd-5aa6-ad6e-5169366c8e79
-- title:
--   Uniqueness of fibre readings over a flat base
-- statement:
--   Let $B_1$ be a commutative local ring with residue field $k = \mathrm{ResidueField}\,B_1$, and let $V$ be a $k$-vector space which is also a $B_1$-module, the two structures being compatible in the sense that the $B_1$-action factors through the residue map, together with an injective $B_1$-linear map $\iota \colon V \to B_1$. Let $f \colon X \to \operatorname{Spec} B_1$ be a flat morphism of schemes, and let $i \colon X_k \to X$, $f_k \colon X_k \to \operatorname{Spec} k$ form a cartesian square over $\operatorname{Spec} B_1 \to \operatorname{Spec} k$ induced by the residue map, that is, $i$, $f_k$, $f$, $\operatorname{Spec}(\mathrm{residue}\,B_1)$ is a pullback square. Let $U \subseteq X$ be an affine open, $W \subseteq X_k$ an open with $W \le i^{-1}U$, and $\delta \in \Gamma(X,U)$. Let $w, w' \colon V^{\vee} \to \Gamma(X_k, W)$ be $k$-linear maps on the $k$-dual of $V$ (the target carrying the $k$-structure coming from $f_k$), and assume each is a fibre reading of $\delta$: for $w$ this means that there are $n$, a family $v \colon \mathrm{Fin}\,n \to V$ and sections $s \colon \mathrm{Fin}\,n \to \Gamma(X,U)$ with $\sum_j \mathrm{algebraMap}\,(\iota(v_j)) \cdot s_j = \delta$ in $\Gamma(X,U)$, the algebra structure on $\Gamma(X,U)$ over $B_1$ being the one induced by $f$, and such that $w(\xi) = \sum_j \xi(v_j) \cdot \left(i^{\sharp}(s_j)\right)|_W$ for every $\xi \in V^{\vee}$; similarly for $w'$, with its own data. The conclusion is $w = w'$.
--
--   This is the well-definedness statement underlying the notion of a fibre reading: the reading of a section $\delta$ of the ideal $\iota(V)\cdot\Gamma(X,U)$ along the fibre is independent of the chosen presentation $\delta = \sum_j \iota(v_j)s_j$. It is used in the construction of Čech cocycles for the Picard deformation and obstruction classes attached to a small extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_IsFibreReading_eq_of_isFibreReading_of_flat.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension
  Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.SmallExtension.IsFibreReading.eq_of_isFibreReading_of_flat
    {B₁ : Type u} [CommRing B₁] [IsLocalRing B₁]
    (V : Type u) [AddCommGroup V] [Module (ResidueField B₁) V] [Module B₁ V] [IsScalarTower B₁ (ResidueField B₁) V]
    (ι : V →ₗ[B₁] B₁) (hι : Function.Injective ι)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) [Flat f]
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of (ResidueField B₁))) (i : Xk ⟶ X)
    (hi : IsPullback i fk f (Spec.map (CommRingCat.ofHom (residue B₁))))
    (U : X.Opens) (hU : IsAffineOpen U) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) (δ : Γ(X, U))
    (w w' : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).obj W)
    (hw : IsFibreReading V ι f fk i U W hW δ w) (hw' : IsFibreReading V ι f fk i U W hW δ w') :
    w = w' := by sorry
