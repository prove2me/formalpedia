-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_ringHom_mulOpposite_forall_apply_eq_of_unitPullback
-- name    : AlgebraicGeometry.OModulePresheaf.exists_ringHom_mulOpposite_forall_apply_eq_of_unitPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/fa37549d-88d4-588a-9edd-f0947f040347
-- title:
--   Ring homomorphism Λ^{op} → End_κ H₁ from pinned pull-backs
-- statement:
--   Let $\kappa$ be a field, $X$ a scheme with a morphism $f_X : X \to \operatorname{Spec}\kappa$, and $L$ a relative group law on $f_X$, i.e. a functorial group structure on the sets $\{\varphi : T \to X \mid \varphi \circ t = f_X\}$ of $T$-points over $\kappa$. Let $\mathcal K$ be an ordered affine cover of $X$ (a finite linearly ordered index set, affine opens whose supremum is $\top$), let $H_1$ be a $\kappa$-vector space, and let $\mathrm{cls}_1$ be a $\kappa$-linear map from the kernel of the degree-one Čech differential $d^1$ of the presheaf `OModulePresheaf.unit` $f_X$ (the presheaf $U \mapsto \Gamma(X,U)$) on $\mathcal K$ to $H_1$. Let $\rho$ assign to each $\varphi : X \to X$ with $\varphi$ followed by $f_X$ equal to $f_X$ a $\kappa$-endomorphism of $H_1$, subject to: $\rho(\mathrm{id}_X) = \mathrm{id}$; $\rho$ of $\varphi$ followed by $\varphi'$ equals $\rho(\varphi) \circ \rho(\varphi')$; if on all $T$-points $P$ the composite $P \circ \chi$ is the $L$-product of $P \circ \varphi$ and $P \circ \varphi'$ then $\rho(\chi) = \rho(\varphi) + \rho(\varphi')$; and a pinning clause: for every ordered affine cover $\mathcal V$, index maps $\mathrm{lam}, \mathrm{lam}'$ with $\mathcal V.U\,v$ contained in $\varphi^{-1}(\mathcal K.U(\mathrm{lam}\,v))$ and in $\mathrm{id}_X^{-1}(\mathcal K.U(\mathrm{lam}'\,v))$ respectively, and $z, z' \in \ker d^1$, if `unitPullback` of $z$ along $\varphi$ minus `unitPullback` of $z'$ along $\mathrm{id}_X$ lies in the image of $d^0$ on $\mathcal V$, then $\rho(\varphi)(\mathrm{cls}_1 z) = \mathrm{cls}_1 z'$. Finally let $\Lambda$ be a ring and $\psi : \Lambda \to \operatorname{Hom}(X,X)$ with each $\psi x$ over $f_X$, $\psi 1 = \mathrm{id}_X$, $\psi(xy) = \psi y$ followed by $\psi x$, and $P \circ \psi(x+y)$ the $L$-product of $P \circ \psi x$ and $P \circ \psi y$ on all $T$-points. The conclusion asserts the existence of a ring homomorphism $\rho_\Lambda : \Lambda^{\mathrm{op}} \to \operatorname{End}_\kappa(H_1)$ satisfying the same pinning clause with $\varphi = \psi x$ and $\rho(\varphi)$ replaced by $\rho_\Lambda(x^{\mathrm{op}})$, for all $x \in \Lambda$.
--
--   This records the standard functoriality of $H^1(X,\mathcal O_X)$ computed by an ordered affine Čech cover as a right action: a ring acting on $X$ by endomorphisms over the base, additively compatible with the relative group law, acts $\kappa$-linearly on the degree-one class module, the contravariance being absorbed into $\Lambda^{\mathrm{op}}$. It supplies the $(\rho_\Lambda, \text{pin})$ datum used in the study of bare deformations of Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_ringHom_mulOpposite_forall_apply_eq_of_unitPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.exists_ringHom_mulOpposite_forall_apply_eq_of_unitPullback
    {κ : Type} [Field κ] {X : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of κ)) (L : RelativeGroupLaw κ fX)
    (𝒦 : X.OrderedAffineCover)
    (H₁ : Type) [AddCommGroup H₁] [Module κ H₁]
    (cls₁ : ↥(LinearMap.ker ((OModulePresheaf.unit fX).d 𝒦 1)) →ₗ[κ] H₁)
    (ρ : ∀ φ : X ⟶ X, φ ≫ fX = fX → (H₁ →ₗ[κ] H₁))
    (hρid : ρ (𝟙 X) (Category.id_comp fX) = LinearMap.id)
    (hρcomp : ∀ (φ φ' : X ⟶ X) (hφ : φ ≫ fX = fX) (hφ' : φ' ≫ fX = fX),
      ρ (φ ≫ φ') (by rw [Category.assoc, hφ', hφ]) = (ρ φ hφ).comp (ρ φ' hφ'))
    (hρadd : ∀ (φ φ' χ : X ⟶ X) (hφ : φ ≫ fX = fX) (hφ' : φ' ≫ fX = fX) (hχ : χ ≫ fX = fX),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (P : SchemeHomOver t fX),
          P.1 ≫ χ = (L.mul t ⟨P.1 ≫ φ, by rw [Category.assoc, hφ]; exact P.2⟩ ⟨P.1 ≫ φ', by rw [Category.assoc, hφ']; exact P.2⟩).1) →
      ρ χ hχ = ρ φ hφ + ρ φ' hφ')
    (hρpin : ∀ (φ : X ⟶ X) (hφ : φ ≫ fX = fX) (𝒱 : X.OrderedAffineCover) (lam lam' : 𝒱.ι → 𝒦.ι)
        (hl : ∀ v, 𝒱.U v ≤ φ ⁻¹ᵁ 𝒦.U (lam v)) (hl' : ∀ v, 𝒱.U v ≤ (𝟙 X) ⁻¹ᵁ 𝒦.U (lam' v))
        (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit fX).d 𝒦 1))),
        OModulePresheaf.unitPullback (πX := fX) φ 𝒱 𝒦 lam hl (0 + 1) z.1 -
            OModulePresheaf.unitPullback (πX := fX) (𝟙 X) 𝒱 𝒦 lam' hl' (0 + 1) z'.1 ∈ LinearMap.range ((OModulePresheaf.unit fX).d 𝒱 0) →
        ρ φ hφ (cls₁ z) = cls₁ z')
    {Λ : Type} [Ring Λ] (ψ : Λ → (X ⟶ X)) (hψ : ∀ x : Λ, ψ x ≫ fX = fX)
    (hψone : ψ 1 = 𝟙 X) (hψmul : ∀ x y : Λ, ψ (x * y) = ψ y ≫ ψ x)
    (hψadd : ∀ (x y : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (P : SchemeHomOver t fX),
      P.1 ≫ ψ (x + y) = (L.mul t ⟨P.1 ≫ ψ x, by rw [Category.assoc, hψ, P.2]⟩ ⟨P.1 ≫ ψ y, by rw [Category.assoc, hψ, P.2]⟩).1) :
    ∃ ρΛ : Λᵐᵒᵖ →+* Module.End κ H₁,
      ∀ (x : Λ) (𝒱 : X.OrderedAffineCover) (lam lam' : 𝒱.ι → 𝒦.ι)
        (hl : ∀ v, 𝒱.U v ≤ ψ x ⁻¹ᵁ 𝒦.U (lam v)) (hl' : ∀ v, 𝒱.U v ≤ (𝟙 X) ⁻¹ᵁ 𝒦.U (lam' v))
        (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit fX).d 𝒦 1))),
        OModulePresheaf.unitPullback (πX := fX) (ψ x) 𝒱 𝒦 lam hl (0 + 1) z.1 -
            OModulePresheaf.unitPullback (πX := fX) (𝟙 X) 𝒱 𝒦 lam' hl' (0 + 1) z'.1 ∈ LinearMap.range ((OModulePresheaf.unit fX).d 𝒱 0) →
        ρΛ (MulOpposite.op x) (cls₁ z) = cls₁ z' := by sorry
