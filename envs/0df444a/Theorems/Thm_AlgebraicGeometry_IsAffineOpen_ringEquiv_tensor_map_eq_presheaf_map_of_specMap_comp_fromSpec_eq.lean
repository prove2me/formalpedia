-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsAffineOpen_ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq
-- name    : AlgebraicGeometry.IsAffineOpen.ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/286bf3d0-11c0-52fe-b27a-ad737dc65f86
-- title:
--   Pinned tensor identifications are compatible with restriction
-- statement:
--   Let $T'$ be a commutative local ring with residue field $k = \mathrm{ResidueField}\,T'$, let $Y, Y', A_k$ be schemes, and let $q_Y : Y \to \operatorname{Spec} T'$, $q_{Y'} : Y' \to \operatorname{Spec} T'$ and $f_k : A_k \to \operatorname{Spec} k$ be morphisms; throughout, a ring of sections $\Gamma(Y, U)$ is regarded as a $T'$-algebra via `algebraOfHom`, that is via the ring map obtained by composing the inverse of the isomorphism $T' \cong \Gamma(\operatorname{Spec} T', \top)$ with $q_Y^\sharp : \Gamma(\operatorname{Spec} T', \top) \to \Gamma(Y, U)$, and similarly for $q_{Y'}$ and for $f_k$ (giving $k$-algebra structures on sections of $A_k$). Let $OU \subseteq Y$ and $OU' \subseteq Y'$ be affine opens, let $W' \le W$ be affine opens of $A_k$, let $m : W \to Y$ be a morphism of schemes, let $h : \Gamma(Y, OU) \to \Gamma(Y', OU')$ be a $T'$-algebra map, and let $\sigma : k \otimes_{T'} \Gamma(Y, OU) \cong \Gamma(A_k, W)$ and $\sigma' : k \otimes_{T'} \Gamma(Y', OU') \cong \Gamma(A_k, W')$ be ring isomorphisms. Assume: (hσ₁) the composite of the isomorphism $W \cong \operatorname{Spec}\Gamma(A_k, W)$ with $\operatorname{Spec}$ of $\sigma$, then $\operatorname{Spec}$ of the inclusion $y \mapsto 1 \otimes y$, then the canonical morphism $\operatorname{Spec}\Gamma(Y, OU) \to Y$, equals $m$; (hσ₂), (hσ'₂) $\sigma(x \otimes 1)$ and $\sigma'(x \otimes 1)$ are the images of $x \in k$ under the structure maps $k \to \Gamma(A_k, W)$, $k \to \Gamma(A_k, W')$ coming from $f_k$; (hcomp) the analogous composite for $W'$, $\sigma'$ and $h$, namely $W' \cong \operatorname{Spec}\Gamma(A_k, W')$ followed by $\operatorname{Spec}$ of $\sigma'$, of $y \mapsto 1 \otimes y$, of $h$, and then $\operatorname{Spec}\Gamma(Y, OU) \to Y$, equals the inclusion $W' \to W$ followed by $m$. The conclusion is that for every $z \in k \otimes_{T'} \Gamma(Y, OU)$ one has $\sigma'\bigl((\mathrm{id}_k \otimes h)(z)\bigr) = \sigma(z)|_{W'}$, the right-hand side being the presheaf restriction $\Gamma(A_k, W) \to \Gamma(A_k, W')$ applied to $\sigma(z)$.
--
--   This is the element-level compatibility statement for two base-change identifications of rings of sections over nested affine opens of a special fibre, each pinned by a geometric condition expressing that it induces a prescribed morphism to the ambient scheme. It is used in the deformation-theoretic cocycle computations for small extensions, in particular by [`AlgebraicGeometry.SmallExtension.d_two_cochain_eq_zero_of_isTangentCoordsOfPairAtVia_pin`](thm.html#AlgebraicGeometry.SmallExtension.d_two_cochain_eq_zero_of_isTangentCoordsOfPairAtVia_pin), [`AlgebraicGeometry.SmallExtension.exists_overlap_isos_cocycle_of_pointDerivations_two_coboundary`](thm.html#AlgebraicGeometry.SmallExtension.exists_overlap_isos_cocycle_of_pointDerivations_two_coboundary) and [`AlgebraicGeometry.SmallExtension.unitPullback_obstruction_two_cocycle_sub_eq_d_of_one_cochain_pin`](thm.html#AlgebraicGeometry.SmallExtension.unitPullback_obstruction_two_cocycle_sub_eq_d_of_one_cochain_pin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsAffineOpen_ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.TwoAffineOpenCover TensorProduct IsLocalRing

universe u

theorem AlgebraicGeometry.IsAffineOpen.ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    {Y Y' Ak : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T')) (qY' : Y' ⟶ Spec (CommRingCat.of T'))
    (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T')))
    (OU : Y.Opens) (hOU : IsAffineOpen OU) (OU' : Y'.Opens) (hOU' : IsAffineOpen OU')
    (W W' : Ak.Opens) (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hWW : W' ≤ W)
    (m : (W : Scheme.{u}) ⟶ Y)
    (h : letI := algebraOfHom qY OU; letI := algebraOfHom qY' OU'
      Γ(Y, OU) →ₐ[T'] Γ(Y', OU'))
    (σ : letI := algebraOfHom qY OU
      (ResidueField T') ⊗[T'] Γ(Y, OU) ≃+* Γ(Ak, W))
    (σ' : letI := algebraOfHom qY' OU'
      (ResidueField T') ⊗[T'] Γ(Y', OU') ≃+* Γ(Ak, W'))
    (hσ₁ : letI := algebraOfHom qY OU
      hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y, OU) →ₐ[T'] (ResidueField T') ⊗[T'] Γ(Y, OU)).toRingHom) ≫
          hOU.fromSpec = m)
    (hσ₂ : letI := algebraOfHom qY OU
      letI := algebraOfHom fk W
      ∀ x : ResidueField T', σ (x ⊗ₜ[T'] (1 : Γ(Y, OU))) = algebraMap (ResidueField T') Γ(Ak, W) x)
    (hσ'₂ : letI := algebraOfHom qY' OU'
      letI := algebraOfHom fk W'
      ∀ x : ResidueField T', σ' (x ⊗ₜ[T'] (1 : Γ(Y', OU'))) = algebraMap (ResidueField T') Γ(Ak, W') x)
    (hcomp : letI := algebraOfHom qY OU
      letI := algebraOfHom qY' OU'
      hW'.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom σ'.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y', OU') →ₐ[T'] (ResidueField T') ⊗[T'] Γ(Y', OU')).toRingHom) ≫
          Spec.map (CommRingCat.ofHom h.toRingHom) ≫ hOU.fromSpec = Ak.homOfLE hWW ≫ m) :
    letI := algebraOfHom qY OU
    letI := algebraOfHom qY' OU'
    ∀ z : (ResidueField T') ⊗[T'] Γ(Y, OU),
      σ' (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h z) =
        (Ak.presheaf.map (homOfLE hWW).op).hom (σ z) := by sorry
