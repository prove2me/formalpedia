-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom
-- name    : AlgebraicGeometry.OModulePresheaf.IsQuasicoherent.exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/67b2d7a5-ebd7-599e-94b6-04c4c68a093d
-- title:
--   Affine-local inverse image of a quasi-coherent module datum
-- statement:
--   Let $A$ be a commutative ring, let $P$ and $V'$ be schemes, and let $q \colon P \to \operatorname{Spec} A$ and $p \colon V' \to P$ be morphisms of schemes. Let $G$ be an `OModulePresheaf` for $q$: an assignment of an abelian group $G(U)$ to every open $U \subseteq P$, carrying an $A$-module structure and a $\Gamma(P,U)$-module structure which are compatible via the $A$-algebra structure on $\Gamma(P,U)$ induced by $q$, together with $A$-linear restriction maps that are semilinear for the restriction of sections and satisfy the identity and composition laws (no sheaf condition). Assume $G$ is quasi-coherent in the sense that for every affine open $U \subseteq P$ and every $f \in \Gamma(P,U)$, each element of $G(P_f)$ becomes the restriction of a section over $U$ after multiplication by some power of $f$, and each section over $U$ restricting to $0$ on the basic open $P_f$ is annihilated by some power of $f$. Then there exist a quasi-coherent `OModulePresheaf` $G'$ for the composite $p$ followed by $q$, and maps $\eta_{U,V} \colon G(U) \to G'(V)$ that are $A$-linear, given for every affine open $U \subseteq P$, every affine open $V \subseteq V'$ and every proof that $V \le p^{-1}U$, such that: $G'$ is coherent (each $G'(V)$ a finite $\Gamma(V',V)$-module on affine opens $V$) whenever $G$ is; each $\eta_{U,V}$ is semilinear along $\Gamma(P,U) \to \Gamma(V',V)$, namely $\eta_{U,V}(a \cdot x) = p^\sharp(a) \cdot \eta_{U,V}(x)$; the $\eta$ are compatible with restriction in $V$ (for $V_1 \le V_2$ both inside $p^{-1}U$, restricting $\eta_{U,V_2}(x)$ to $V_1$ gives $\eta_{U,V_1}(x)$) and in $U$ (for $U_1 \le U_2$ both containing $p(V)$, $\eta_{U_2,V}(x) = \eta_{U_1,V}(G.\mathrm{res}(x))$); for every such pair $(U,V)$, with $\Gamma(V',V)$ regarded as a $\Gamma(P,U)$-algebra via $p^\sharp$, there is a $\Gamma(V',V)$-linear isomorphism $\beta \colon \Gamma(V',V) \otimes_{\Gamma(P,U)} G(U) \xrightarrow{\sim} G'(V)$ with $\beta(1 \otimes x) = \eta_{U,V}(x)$; and for affine opens $W \subseteq P$, $W' \subseteq V'$ with $W' = p^{-1}W$ exactly, if the induced morphism $p \mid_W$ is an isomorphism then $\eta_{W,W'}$ is bijective.
--
--   This is the existence of the inverse image $p^{*}G$ of a quasi-coherent module, packaged not as a sheaf but as an affine-local datum: the modules $G'(V)$ together with unit maps exhibiting them as base changes $\Gamma(V',V) \otimes_{\Gamma(P,U)} G(U)$. It is used in the refinement that additionally controls kernels, [`AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_forall_exists_linearEquiv_tensorProduct_of_hom`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_forall_exists_linearEquiv_tensorProduct_of_hom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.OModulePresheaf.IsQuasicoherent.exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom
    {A : Type u} [CommRing A]
    {P V' : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) (p : V' ⟶ P)
    (G : OModulePresheaf q) (hq : G.IsQuasicoherent) :
    ∃ (G' : OModulePresheaf (p ≫ q))
      (η : ∀ (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → (G.obj U.1 →ₗ[A] G'.obj V.1)),
      G'.IsQuasicoherent ∧ (G.IsCoherent → G'.IsCoherent) ∧

      (∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (a : Γ(P, U.1)) (x : G.obj U.1),
        η U V h (a • x) = (p.appLE U.1 V.1 h).hom a • η U V h x) ∧

      (∀ (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
        (hV : V₁.1 ≤ V₂.1) (x : G.obj U.1), G'.res hV (η U V₂ h₂ x) = η U V₁ h₁ x) ∧

      (∀ (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
        (hU : U₁.1 ≤ U₂.1) (x : G.obj U₂.1), η U₂ V h₂ x = η U₁ V h₁ (G.res hU x)) ∧

      (∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1),
        letI := (p.appLE U.1 V.1 h).hom.toAlgebra
        ∃ β : Γ(V', V.1) ⊗[Γ(P, U.1)] G.obj U.1 ≃ₗ[Γ(V', V.1)] G'.obj V.1,
          ∀ x : G.obj U.1, β (1 ⊗ₜ x) = η U V h x) ∧

      (∀ (W : P.affineOpens) (W' : V'.affineOpens) (hW : W'.1 = p ⁻¹ᵁ W.1),
        IsIso (p ∣_ W.1) → Function.Bijective (η W W' hW.le)) := by sorry
