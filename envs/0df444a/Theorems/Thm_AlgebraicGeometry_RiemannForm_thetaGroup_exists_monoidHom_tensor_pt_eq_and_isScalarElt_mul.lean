-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tensor_pt_eq_and_isScalarElt_mul
-- name    : AlgebraicGeometry.RiemannForm.thetaGroup.exists_monoidHom_tensor_pt_eq_and_isScalarElt_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/a19a09b8-47ce-5fcd-a07e-66d8c3529cb5
-- title:
--   Tensor multiplicativity of theta groups
-- statement:
--   Let $k$ be a field, let $A$ be a scheme, let $f : A \to \operatorname{Spec} k$ be a morphism, let $L$ be a relative group law on $f$ (a functorial group structure on the sets $\mathrm{Hom}_{\operatorname{Spec} k}(T, A)$, compatible with base change along $T' \to T$), let $hc$ witness that $L$ is commutative, and let $M_1, M_2$ be sheaves of modules on $A$. For a module $M$, $\mathrm{thetaGroup}\ f\ L\ hc\ M$ is the subgroup of $\mathrm{Aut}(A, M) \times \mathrm{Multiplicative}(L.\mathrm{AlgPoints}\ hc\ k)$ consisting of pairs $(a, P)$ whose underlying automorphism of $A$ is the translation by the point attached to $P$, and $\mathrm{pt}$ is the homomorphism recording $P$. The assertion is that there exists a monoid homomorphism $\tau$ from the subgroup of pairs $(g_1, g_2) \in \mathrm{thetaGroup}(M_1) \times \mathrm{thetaGroup}(M_2)$ with $\mathrm{pt}(g_1) = \mathrm{pt}(g_2)$ (the equaliser of $\mathrm{pt}$ composed with the two projections) to $\mathrm{thetaGroup}(M_1 \otimes M_2)$ such that, first, $\mathrm{pt}(\tau(g_1,g_2)) = \mathrm{pt}(g_1)$ for every such pair, and second, for all $c_1, c_2 \in k$, if $g_1$ lies over the identity point with unit reading multiplication by the constant $c_1$, and $g_2$ likewise with constant $c_2$, then $\tau(g_1, g_2)$ lies over the identity point with unit reading multiplication by the constant $c_1 c_2$. Only existence is asserted, with no uniqueness or explicit formula.
--
--   This is the multiplicativity of Mumford's theta group in the sheaf variable: theta-group elements over a common point tensor together, and the central scalars multiply. It is used for the power map on theta groups and, through it, for the computation of the level pairing from commutators of theta-group elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tensor_pt_eq_and_isScalarElt_mul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ThetaGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.thetaGroup.exists_monoidHom_tensor_pt_eq_and_isScalarElt_mul
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (M₁ M₂ : A.Modules) :
    ∃ τ : MonoidHom.eqLocus
          ((thetaGroup.pt f L hc M₁).comp (MonoidHom.fst (thetaGroup f L hc M₁) (thetaGroup f L hc M₂)))
          ((thetaGroup.pt f L hc M₂).comp (MonoidHom.snd (thetaGroup f L hc M₁) (thetaGroup f L hc M₂))) →*
        thetaGroup f L hc (M₁ ⊗ M₂),
      (∀ p, thetaGroup.pt f L hc (M₁ ⊗ M₂) (τ p) = thetaGroup.pt f L hc M₁ p.1.1) ∧
      (∀ p (c₁ c₂ : k), thetaGroup.IsScalarElt f L hc M₁ p.1.1 c₁ → thetaGroup.IsScalarElt f L hc M₂ p.1.2 c₂ →
        thetaGroup.IsScalarElt f L hc (M₁ ⊗ M₂) (τ p) (c₁ * c₂)) := by sorry
