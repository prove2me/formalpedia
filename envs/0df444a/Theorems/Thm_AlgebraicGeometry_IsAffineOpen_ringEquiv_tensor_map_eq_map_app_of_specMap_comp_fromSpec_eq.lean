-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsAffineOpen_ringEquiv_tensor_map_eq_map_app_of_specMap_comp_fromSpec_eq
-- name    : AlgebraicGeometry.IsAffineOpen.ringEquiv_tensor_map_eq_map_app_of_specMap_comp_fromSpec_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/3d569e1d-8d55-5311-8e0d-15bbab5d75c2
-- title:
--   Transport of σ along a morphism of special fibres
-- statement:
--   Let $T'$ be a local ring with residue field $k=\mathrm{ResidueField}\,T'$, and let $Y,Y',A_k,X_k$ be schemes equipped with structure morphisms $q_Y\colon Y\to\operatorname{Spec} T'$, $q_{Y'}\colon Y'\to\operatorname{Spec} T'$, $f_k\colon A_k\to\operatorname{Spec} k$, $f^X_k\colon X_k\to\operatorname{Spec} k$, together with $h_k\colon X_k\to A_k$ satisfying $h_k$ followed by $f_k$ equals $f^X_k$. Fix affine opens $OU\subseteq Y$, $OU'\subseteq Y'$, $W\subseteq A_k$, $W'\subseteq X_k$ with $W'\le h_k^{-1}W$, and a morphism $m\colon W\to Y$ from the affine scheme $W$. Throughout, sections over an open are regarded as algebras over the base ring by `algebraOfHom`, i.e. via the inverse of $\Gamma\!\operatorname{Spec}$ composed with the appropriate `appLE` map of the structure morphism. Given a $T'$-algebra map $h\colon\Gamma(Y,OU)\to\Gamma(Y',OU')$ and ring isomorphisms $\sigma\colon k\otimes_{T'}\Gamma(Y,OU)\xrightarrow{\sim}\Gamma(A_k,W)$, $\sigma'\colon k\otimes_{T'}\Gamma(Y',OU')\xrightarrow{\sim}\Gamma(X_k,W')$ such that: $\sigma$ and $\sigma'$ send $x\otimes 1$ to the image of $x$ under the respective structure maps from $k$; $\operatorname{Spec}$ of $\sigma\circ\text{includeRight}$, read through $W\cong\operatorname{Spec}\Gamma(A_k,W)$ and $\operatorname{Spec}\Gamma(Y,OU)\to Y$, equals $m$; and $\operatorname{Spec}$ of $\sigma'\circ\text{includeRight}\circ h$, read the same way, equals $W'\to h_k^{-1}W\to W$ followed by $m$ — then for every $z\in k\otimes_{T'}\Gamma(Y,OU)$ one has $\sigma'\bigl((\mathrm{id}_k\otimes h)(z)\bigr)=h_k^{\ast}(\sigma z)\big|_{W'}$, the right-hand side being the image of $\sigma z$ under $\Gamma(A_k,W)\to\Gamma(X_k,h_k^{-1}W)\to\Gamma(X_k,W')$.
--
--   This is the compatibility statement used to transport chart-wise identifications of the special fibre of a deformation along a morphism $h_k\colon X_k\to A_k$ of special fibres: the two pinning conditions, expressed as equalities of morphisms of affine schemes, force the algebraic identity between $\mathrm{id}_k\otimes h$ and pullback-then-restriction of sections. It is applied in the computation of the obstruction two-cocycle attached to a unit pullback of a small extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsAffineOpen_ringEquiv_tensor_map_eq_map_app_of_specMap_comp_fromSpec_eq.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TensorProduct Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.IsAffineOpen.ringEquiv_tensor_map_eq_map_app_of_specMap_comp_fromSpec_eq
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    {Y Y' Ak Xk : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T')) (qY' : Y' ⟶ Spec (CommRingCat.of T'))
    (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (fXk : Xk ⟶ Spec (CommRingCat.of (ResidueField T')))
    (hk : Xk ⟶ Ak) (hhkf : hk ≫ fk = fXk)
    (OU : Y.Opens) (hOU : IsAffineOpen OU) (OU' : Y'.Opens) (hOU' : IsAffineOpen OU')
    (W : Ak.Opens) (W' : Xk.Opens) (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hWW : W' ≤ hk ⁻¹ᵁ W)
    (m : (W : Scheme.{u}) ⟶ Y)
    (h : letI := algebraOfHom qY OU; letI := algebraOfHom qY' OU'
      Γ(Y, OU) →ₐ[T'] Γ(Y', OU'))
    (σ : letI := algebraOfHom qY OU
      (ResidueField T') ⊗[T'] Γ(Y, OU) ≃+* Γ(Ak, W))
    (σ' : letI := algebraOfHom qY' OU'
      (ResidueField T') ⊗[T'] Γ(Y', OU') ≃+* Γ(Xk, W'))
    (hσ₁ : letI := algebraOfHom qY OU
      hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y, OU) →ₐ[T'] (ResidueField T') ⊗[T'] Γ(Y, OU)).toRingHom) ≫
          hOU.fromSpec = m)
    (hσ₂ : letI := algebraOfHom qY OU
      letI := algebraOfHom fk W
      ∀ x : ResidueField T', σ (x ⊗ₜ[T'] (1 : Γ(Y, OU))) = algebraMap (ResidueField T') Γ(Ak, W) x)
    (hσ'₂ : letI := algebraOfHom qY' OU'
      letI := algebraOfHom fXk W'
      ∀ x : ResidueField T', σ' (x ⊗ₜ[T'] (1 : Γ(Y', OU'))) = algebraMap (ResidueField T') Γ(Xk, W') x)
    (hcomp : letI := algebraOfHom qY OU
      letI := algebraOfHom qY' OU'
      hW'.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom σ'.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y', OU') →ₐ[T'] (ResidueField T') ⊗[T'] Γ(Y', OU')).toRingHom) ≫
          Spec.map (CommRingCat.ofHom h.toRingHom) ≫ hOU.fromSpec = Xk.homOfLE hWW ≫ (hk ∣_ W) ≫ m) :
    letI := algebraOfHom qY OU
    letI := algebraOfHom qY' OU'
    ∀ z : (ResidueField T') ⊗[T'] Γ(Y, OU),
      σ' (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h z) =
        (Xk.presheaf.map (homOfLE hWW).op).hom ((hk.app W).hom (σ z)) := by sorry
