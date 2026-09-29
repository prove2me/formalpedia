-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_sections_pullback_tensor_of_isAffineHom_of_isAffineOpen
-- name    : AlgebraicGeometry.exists_ringEquiv_sections_pullback_tensor_of_isAffineHom_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/ffcdc1c4-f791-5653-b05e-157a6bb7ceec
-- title:
--   Sections of an affine pullback over an affine chart
-- statement:
--   Let $X$, $Y$, $Z$ be schemes, let $a \colon X \to Z$ and $b \colon Y \to Z$ be affine morphisms, let $U$ be an open subset of $Z$ which is an affine open, and assume the inclusion of opens $\mathrm{pr}_1^{-1}(a^{-1}U) \le \mathrm{pr}_2^{-1}(b^{-1}U)$ inside the pullback $X \times_Z Y$, where $\mathrm{pr}_1 =$ `pullback.fst a b` and $\mathrm{pr}_2 =$ `pullback.snd a b`. Regard $\Gamma(X, a^{-1}U)$ and $\Gamma(Y, b^{-1}U)$ as algebras over $R = \Gamma(Z, U)$ via the ring maps induced by $a$ and $b$ on sections over $U$. The conclusion is twofold: first, the open $\mathrm{pr}_1^{-1}(a^{-1}U)$ of $X \times_Z Y$ is an affine open; second, there exists a ring isomorphism $$\tau \colon \Gamma\bigl(X \times_Z Y,\ \mathrm{pr}_1^{-1}(a^{-1}U)\bigr) \;\xrightarrow{\ \sim\ }\; \Gamma(X, a^{-1}U) \otimes_{R} \Gamma(Y, b^{-1}U)$$ (an isomorphism of rings, not asserted to be $R$-linear as such) which sends the pullback of a section $s \in \Gamma(X, a^{-1}U)$ along $\mathrm{pr}_1$ to $s \otimes 1$, and the pullback of a section $s' \in \Gamma(Y, b^{-1}U)$ along $\mathrm{pr}_2$, restricted to $\mathrm{pr}_1^{-1}(a^{-1}U)$ using the given inclusion of opens, to $1 \otimes s'$.
--
--   This is the standard affine-local description of a fibre product: over an affine chart $U \subseteq Z$ the two affine preimages glue to the affine open $\operatorname{Spec}\bigl(\Gamma(X,a^{-1}U) \otimes_{\Gamma(Z,U)} \Gamma(Y,b^{-1}U)\bigr)$ of $X \times_Z Y$, with the two projections corresponding to the two tensor inclusions. It is used in the treatment of relative group laws and of abelian schemes, where the shear morphism and coaction maps are analysed chart by chart on global sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_ringEquiv_sections_pullback_tensor_of_isAffineHom_of_isAffineOpen.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem AlgebraicGeometry.exists_ringEquiv_sections_pullback_tensor_of_isAffineHom_of_isAffineOpen
    {X Y Z : Scheme.{u}} (a : X ⟶ Z) (b : Y ⟶ Z) [IsAffineHom a] [IsAffineHom b]
    (U : Z.Opens) (hU : IsAffineOpen U)
    (hle₂ : (pullback.fst a b) ⁻¹ᵁ (a ⁻¹ᵁ U) ≤ (pullback.snd a b) ⁻¹ᵁ (b ⁻¹ᵁ U)) :
    letI : Algebra Γ(Z, U) Γ(X, a ⁻¹ᵁ U) := (a.app U).hom.toAlgebra
    letI : Algebra Γ(Z, U) Γ(Y, b ⁻¹ᵁ U) := (b.app U).hom.toAlgebra
    IsAffineOpen ((pullback.fst a b) ⁻¹ᵁ (a ⁻¹ᵁ U)) ∧
    ∃ τ : Γ(pullback a b, (pullback.fst a b) ⁻¹ᵁ (a ⁻¹ᵁ U)) ≃+* Γ(X, a ⁻¹ᵁ U) ⊗[Γ(Z, U)] Γ(Y, b ⁻¹ᵁ U),
      (∀ s : Γ(X, a ⁻¹ᵁ U), τ (((pullback.fst a b).app (a ⁻¹ᵁ U)).hom s) = s ⊗ₜ 1) ∧
      (∀ s' : Γ(Y, b ⁻¹ᵁ U),
        τ (((pullback.snd a b).appLE (b ⁻¹ᵁ U) ((pullback.fst a b) ⁻¹ᵁ (a ⁻¹ᵁ U)) hle₂).hom s') = 1 ⊗ₜ s') := by sorry
