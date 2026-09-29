-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct
-- name    : AlgebraicGeometry.OModulePresheaf.exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/246abc75-7f59-5933-82ec-65630cbcfada
-- title:
--   Pull-back of a morphism of quasi-coherent module data
-- statement:
--   Let $A$ be a commutative ring, let $q \colon P \to \operatorname{Spec} A$ and $p \colon V' \to P$ be morphisms of schemes, and let $G_1, G_2$ be $\mathcal O$-module data over $q$: to each open $U \subseteq P$ an $A$-module which is also a $\Gamma(P,U)$-module compatibly, together with restriction maps that are $A$-linear and semilinear over restriction of functions and functorial. Assume $G_1, G_2$ are quasi-coherent in the sense that for every affine open $U$ and $f \in \Gamma(P,U)$ every section over the basic open $D(f)$ becomes, after multiplication by some power of $f$, a restriction of a section over $U$, and a section over $U$ restricting to $0$ is annihilated by a power of $f$. Let $G'_1, G'_2$ be quasi-coherent $\mathcal O$-module data over $p$ followed by $q$, presented as inverse images: for affine opens $U \subseteq P$, $V \subseteq V'$ with $V \le p^{-1}U$ there are $A$-linear maps $\eta_{i,U,V} \colon G_i(U) \to G'_i(V)$, semilinear over $p^\sharp =$ `p.appLE`, compatible with shrinking $V$ and with shrinking $U$, and such that $\eta_{i,U,V}$ induces a $\Gamma(V',V)$-linear isomorphism $\Gamma(V',V) \otimes_{\Gamma(P,U)} G_i(U) \cong G'_i(V)$ sending $1 \otimes x$ to $\eta_{i,U,V}(x)$. Given a morphism $\psi$ of $\mathcal O$-module data $G_1 \to G_2$ on affine opens (an $A$-linear, $\Gamma(P,U)$-linear family commuting with restrictions), there exists such a morphism $\psi' \colon G'_1 \to G'_2$ with $\psi'_V \circ \eta_{1,U,V} = \eta_{2,U,V} \circ \psi_U$ for all charts $(U,V)$, such that: if every $\psi_U$ ($U$ affine open in $P$) is surjective then every $\psi'_V$ ($V$ affine open in $V'$) is surjective; and if moreover $\ker \psi_U = J \cdot G_1(U)$ for all affine $U$, for an ideal $J \subseteq A$, then $\ker \psi'_V = J \cdot G'_1(V)$ for all affine $V$.
--
--   This is the construction of the inverse image $p^{*}\psi$ of a morphism of quasi-coherent modules, together with the right exactness of pull-back: surjectivity and a kernel of the shape $J\cdot(-)$ are preserved. It is used in the construction of coherent module data with prescribed kernels on a scheme over $\operatorname{Spec} A$ obtained by base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct
    {A : Type u} [CommRing A]
    {P V' : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) (p : V' ⟶ P)
    (G₁ G₂ : OModulePresheaf q) (hq₁ : G₁.IsQuasicoherent) (hq₂ : G₂.IsQuasicoherent)
    (G'₁ : OModulePresheaf (p ≫ q)) (hq'₁ : G'₁.IsQuasicoherent)
    (η₁ : ∀ (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → (G₁.obj U.1 →ₗ[A] G'₁.obj V.1))
    (hη₁s : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (a : Γ(P, U.1)) (x : G₁.obj U.1),
      η₁ U V h (a • x) = (p.appLE U.1 V.1 h).hom a • η₁ U V h x)
    (hη₁V : ∀ (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
      (hV : V₁.1 ≤ V₂.1) (x : G₁.obj U.1), G'₁.res hV (η₁ U V₂ h₂ x) = η₁ U V₁ h₁ x)
    (hη₁U : ∀ (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
      (hU : U₁.1 ≤ U₂.1) (x : G₁.obj U₂.1), η₁ U₂ V h₂ x = η₁ U₁ V h₁ (G₁.res hU x))
    (hβ₁ : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1),
      letI := (p.appLE U.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U.1)] G₁.obj U.1 ≃ₗ[Γ(V', V.1)] G'₁.obj V.1,
        ∀ x : G₁.obj U.1, β (1 ⊗ₜ x) = η₁ U V h x)
    (G'₂ : OModulePresheaf (p ≫ q)) (hq'₂ : G'₂.IsQuasicoherent)
    (η₂ : ∀ (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → (G₂.obj U.1 →ₗ[A] G'₂.obj V.1))
    (hη₂s : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (a : Γ(P, U.1)) (x : G₂.obj U.1),
      η₂ U V h (a • x) = (p.appLE U.1 V.1 h).hom a • η₂ U V h x)
    (hη₂V : ∀ (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
      (hV : V₁.1 ≤ V₂.1) (x : G₂.obj U.1), G'₂.res hV (η₂ U V₂ h₂ x) = η₂ U V₁ h₁ x)
    (hη₂U : ∀ (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
      (hU : U₁.1 ≤ U₂.1) (x : G₂.obj U₂.1), η₂ U₂ V h₂ x = η₂ U₁ V h₁ (G₂.res hU x))
    (hβ₂ : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1),
      letI := (p.appLE U.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U.1)] G₂.obj U.1 ≃ₗ[Γ(V', V.1)] G'₂.obj V.1,
        ∀ x : G₂.obj U.1, β (1 ⊗ₜ x) = η₂ U V h x)
    (ψ : OModulePresheaf.AffHom G₁ G₂) :
    ∃ ψ' : OModulePresheaf.AffHom G'₁ G'₂,
      (∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (x : G₁.obj U.1),
        ψ'.app V (η₁ U V h x) = η₂ U V h (ψ.app U x)) ∧
      ((∀ U : P.affineOpens, Function.Surjective (ψ.app U)) →
        ∀ V : V'.affineOpens, Function.Surjective (ψ'.app V)) ∧
      (∀ J : Ideal A, (∀ U : P.affineOpens, Function.Surjective (ψ.app U)) →
        (∀ U : P.affineOpens, LinearMap.ker (ψ.app U) = J • (⊤ : Submodule A (G₁.obj U.1))) →
        ∀ V : V'.affineOpens, LinearMap.ker (ψ'.app V) = J • (⊤ : Submodule A (G'₁.obj V.1))) := by sorry
