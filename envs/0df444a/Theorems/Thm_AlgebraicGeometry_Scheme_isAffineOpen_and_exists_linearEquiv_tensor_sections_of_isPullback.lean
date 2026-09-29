-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback
-- name    : AlgebraicGeometry.Scheme.isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/a3e6a722-1f1f-562d-a2e7-e5254b0a7677
-- title:
--   Sections on p₁⁻¹U∩ p₂⁻¹V as a tensor product
-- statement:
--   Let $R$ be a commutative ring, let $X$, $Y$, $P$ be schemes, and let $f_X \colon X \to \operatorname{Spec} R$ and $f_Y \colon Y \to \operatorname{Spec} R$ be morphisms. Let $p_1 \colon P \to X$ and $p_2 \colon P \to Y$ be morphisms such that the square formed by $p_1$, $p_2$, $f_X$, $f_Y$ is a pullback square (`IsPullback p₁ p₂ fX fY`), so $P$ is a fibre product of $X$ and $Y$ over $\operatorname{Spec} R$, not necessarily Mathlib's chosen one. Let $U$ be an open of $X$ with $U$ affine and $V$ an open of $Y$ with $V$ affine. The three $R$-algebra structures in force are those produced by `Scheme.TwoAffineOpenCover.algebraOfHom`: for a morphism $c$ to $\operatorname{Spec} R$ and an open $W$ of the source, $R$ acts on $\Gamma$ of $W$ through the ring map obtained by composing the inverse of the canonical isomorphism $\Gamma(\operatorname{Spec} R) \cong R$ with $c.\mathrm{appLE}\ \top\ W$; here they are taken for $f_X$ on $U$, for $f_Y$ on $V$, and for $p_1 \ggg f_X$ on $W := p_1^{-1}U \sqcap p_2^{-1}V$. The conclusion is twofold: $W$ is an affine open of $P$, and there is an isomorphism $\Phi$ of $R$-modules from $\Gamma(X,U) \otimes_R \Gamma(Y,V)$ onto $\Gamma(P,W)$ such that for all $a \in \Gamma(X,U)$ and $b \in \Gamma(Y,V)$ one has $\Phi(a \otimes b) = p_1^{\sharp}(a)|_W \cdot p_2^{\sharp}(b)|_W$, the two factors being the images under $p_1.\mathrm{appLE}\ U\ W$ and $p_2.\mathrm{appLE}\ V\ W$. Note that $\Phi$ is asserted only to be $R$-linear, although the formula on pure tensors together with linearity forces it to be a ring map as well.
--
--   This is the standard description of a fibre product by gluing the affine charts $\operatorname{Spec}(\Gamma(X,U) \otimes_R \Gamma(Y,V))$, stated for an arbitrary cartesian square rather than for Mathlib's chosen pullback. It is used in the treatment of $\mathcal{O}$-module presheaves on products, for instance in computations of Čech invariants of box products and in the construction of natural isomorphisms identifying sections of a box product with tensor products of sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem AlgebraicGeometry.Scheme.isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback
    {R : Type u} [CommRing R] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of R)) (fY : Y ⟶ Spec (CommRingCat.of R))
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom fX U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom fY V
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (p₁ ≫ fX) (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V)
    IsAffineOpen (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) ∧
    ∃ Φ : Γ(X, U) ⊗[R] Γ(Y, V) ≃ₗ[R] Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V),
      ∀ (a : Γ(X, U)) (b : Γ(Y, V)), Φ (a ⊗ₜ[R] b) =
        (p₁.appLE U (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) inf_le_left).hom a *
          (p₂.appLE V (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) inf_le_right).hom b := by sorry
