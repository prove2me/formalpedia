-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_trivialModDeformations_map_H1_tensor_natural
-- name    : AlgebraicGeometry.RelPicard.exists_trivialModDeformations_map_H1_tensor_natural
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/70f6c1da-6ae9-581f-8b42-8daaf2e548c2
-- title:
--   First-order deformations of the trivial bundle and Čech H¹
-- statement:
--   Let $K$ be a field, let $C$ be a scheme with a morphism $c : C \to \operatorname{Spec} K$, let $\varepsilon$ be a section of $c$, that is a morphism $\operatorname{Spec} K \to C$ whose composite with $c$ is the identity, and let $\mathcal V$ consist of two open subschemes $U_0, U_1$ of $C$ with $U_0, U_1$ and $U_0 \cap U_1$ affine and $U_0 \cup U_1 = C$. Write $H^1$ for the Čech first cohomology of the structure sheaf attached to this two-chart cover, namely the quotient of the ring of sections on the overlap by the image of the Čech differential. For a $K$-vector space $V$ (given as an abelian group with commuting left $K$- and right $K$-actions that agree), $\mathrm{TrivialModDeformations}\ c\ \varepsilon\ V$ is the type of pairs consisting of a rigidified line bundle over $C \times_{\operatorname{Spec} K} \operatorname{Spec}(K \oplus V)$, $K \oplus V$ being the trivial square-zero extension — that is, an invertible module $L$ on this fibre product together with a trivialisation of its pullback along the section induced by $\varepsilon$ — whose pullback along the base point $\operatorname{Spec} K \to \operatorname{Spec}(K \oplus V)$ is isomorphic to the unit module. The assertion is that there is a family of maps $\beta_V : \mathrm{TrivialModDeformations}\ c\ \varepsilon\ V \to H^1 \otimes_K V$, one for every such $V$ in the same universe, such that: (i) $\beta_V(L) = \beta_V(L')$ if and only if the underlying modules of $L$ and $L'$ are isomorphic (rigidifications being disregarded); (ii) each $\beta_V$ is surjective; (iii) for every $K$-linear map $\varphi : V \to W$ and every $L$, $\beta_W$ of the pullback of $L$ along the morphism $\operatorname{Spec}(K \oplus W) \to \operatorname{Spec}(K \oplus V)$ induced by $\varphi$ equals $\mathrm{id}_{H^1} \otimes \varphi$ applied to $\beta_V(L)$.
--
--   This is the computation of the Picard group of a trivial square-zero thickening: first-order deformations of the trivial line bundle with coefficients in $V$ are classified, up to isomorphism of the underlying invertible module, by $H^1(C,\mathcal O_C) \otimes_K V$, functorially in $V$. It is the input to the identification of the tangent space at the zero section of a relative Picard functor, used in [`AlgebraicCurve.CurveModel.finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic`](thm.html#AlgebraicCurve.CurveModel.finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic) to compute the dimension of that space in terms of the genus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_trivialModDeformations_map_H1_tensor_natural.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.exists_trivialModDeformations_map_H1_tensor_natural
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) (𝒱 : C.TwoAffineOpenCover) :
    ∃ β : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V],
        TrivialModDeformations c ε V → (𝒱.structureSheafSections c).H1 ⊗[K] V,
      (∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
          (L L' : TrivialModDeformations c ε V), β V L = β V L' ↔ Nonempty (L.1.L ≅ L'.1.L)) ∧
      (∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V],
          Function.Surjective (β V)) ∧
      (∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
          (W : Type u) [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]
          (φ : V →ₗ[K] W) (L : TrivialModDeformations c ε V),
          β W (L.map φ) = LinearMap.lTensor ((𝒱.structureSheafSections c).H1) φ (β V L)) := by sorry
