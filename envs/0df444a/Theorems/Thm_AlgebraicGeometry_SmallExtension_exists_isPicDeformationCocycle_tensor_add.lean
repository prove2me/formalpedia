-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_tensor_add
-- name    : AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_tensor_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/ea63d396-3808-5216-a5af-5667d24f1eab
-- title:
--   Picard deformation cocycles add under tensor product
-- statement:
--   Let $B_1$ be a commutative ring, $k$ a field, and $V$ an abelian group carrying both a $k$-module and a $B_1$-module structure, with $\iota : V \to B_1$ a $B_1$-linear map whose image is square-zero, i.e. $\iota(v)\iota(w)=0$ for all $v,w \in V$. Let $f : X \to \operatorname{Spec} B_1$, let $g : X_0 \to X$ and $i : X_k \to X$ be affine morphisms, let $f_k : X_k \to \operatorname{Spec} k$, and let $\mathcal U$ be an ordered affine cover of $X$ (a finite linearly ordered family of affine opens with supremum $\top$). Let $M, M'$ be sheaves of modules on $X$, let $\varphi_0, \varphi_0'$ trivialise their pullbacks along $g$, i.e. be isomorphisms $g^*M \cong \mathcal O_{X_0}$, $g^*M' \cong \mathcal O_{X_0}$, and let $w, w'$ be $k$-linear maps from $\operatorname{Hom}_k(V,k)$ to the $1$-cochains of the presheaf $\mathcal O_{X_k}$ on the cover $\mathcal U$ pulled back along $i$. Assume `IsPicDeformationCocycle` holds for $(M,\varphi_0,w)$ and for $(M',\varphi_0',w')$: for each there are a Čech trivialisation $\tau$ of the module on the charts $\mathcal U$, sections $e_a, e'_a \in \Gamma(X, \mathcal U_a)$ with $e_a e'_a = 1$, such that $g^\#(e_a)$ is the section of the unit sheaf obtained from the automorphism comparing the pullback of $\tau$ along $g$ with the given trivialisation, and such that on each $1$-simplex $s$ the section $\tau_s \, e'_{s_0}|\, e_{s_1}| - 1$ is a fibre reading of the corresponding component of the cochain: it is written as $\sum_j \iota(v_j)s_j$ with the cochain sending $\xi$ to $\sum_j \xi(v_j)\,(i^\# s_j)$ restricted to the intersection. The conclusion asserts the existence of an isomorphism $\Phi : g^*(M \otimes M') \cong \mathcal O_{X_0}$ for which `IsPicDeformationCocycle` holds for $(M \otimes M', \Phi, w + w')$, the tensor product being taken in the monoidal structure on sheaves of modules on $X$.
--
--   This is the additivity of the deformation-theoretic Čech description of the relative Picard group: tensoring two line-bundle deformations with prescribed first-order data adds the associated cocycles. Only existence of a trivialisation $\Phi$ of the reduction of $M \otimes M'$ is asserted, rather than the canonical one coming from the monoidal structure of pullback; it is used in the Čerednik–Drinfel'd fake elliptic curve material, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_tensor_self_iso_of_pullback_iso_unit_of_isUnit_two`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_tensor_self_iso_of_pullback_iso_unit_of_isUnit_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_tensor_add.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension
  Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_tensor_add
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    {X₀ : Scheme.{u}} (g : X₀ ⟶ X) [IsAffineHom g]
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X) [IsAffineHom i]
    (𝒰 : X.OrderedAffineCover)
    (hJ : ∀ v w : V, ι v * ι w = 0)
    (M M' : X.Modules)
    (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (φ₀' : (Scheme.Modules.pullback g).obj M' ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (w w' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w) (hw' : IsPicDeformationCocycle V ι f fk i g 𝒰 M' φ₀' w') :
    ∃ Φ : (Scheme.Modules.pullback g).obj (M ⊗ M') ≅ SheafOfModules.unit X₀.ringCatSheaf,
      IsPicDeformationCocycle V ι f fk i g 𝒰 (M ⊗ M') Φ (w + w') := by sorry
