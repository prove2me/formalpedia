-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tpow_pt_eq_and_isScalarElt_pow
-- name    : AlgebraicGeometry.RiemannForm.thetaGroup.exists_monoidHom_tpow_pt_eq_and_isScalarElt_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/bebf9ed5-4c26-52c8-b84d-a6c8e2c0f9ce
-- title:
--   Theta group homomorphism into tensor powers, raising scalars to the nth power
-- statement:
--   Let $k$ be a field and $f : A \to \operatorname{Spec} k$ a morphism of schemes, let $L$ be a relative group law on $f$ (a functorial group structure, compatible with base change, on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points of $A$ over $\operatorname{Spec} k$), let $hc$ assert that $L$ is commutative, let $M$ be an object of `A.Modules`, and let $n$ be a natural number with $1 \le n$. Here `thetaGroup f L hc N` denotes the subgroup of $\operatorname{Aut}(\langle A, N\rangle) \times \operatorname{Multiplicative}(L.\mathrm{AlgPoints}\ hc\ k)$ of those pairs whose automorphism has base morphism the $L$-translation by the point attached to the second component, `thetaGroup.pt` records that point, and `thetaGroup.IsScalarElt f L hc N g c` says that $g$ has trivial point and that the resulting endomorphism `unitReading` of $N$ acts on sections as multiplication by the image of $c \in k$ in $\mathcal{O}_A$. The assertion is that there exists a group homomorphism $\rho : \mathrm{thetaGroup}\ f\ L\ hc\ M \to \mathrm{thetaGroup}\ f\ L\ hc\ (\mathrm{tpow}\ M\ n)$ into the theta group of the $n$-fold tensor power $\mathrm{tpow}\ M\ n$ (defined by $\mathrm{tpow}\ M\ 0 = \mathbf 1$ and $\mathrm{tpow}\ M\ (m+1) = \mathrm{tpow}\ M\ m \otimes M$) such that every $g$ has $\mathrm{pt}(\rho g) = \mathrm{pt}(g)$, and such that whenever $g$ is the scalar $c \in k$ in the above sense, $\rho g$ is the scalar $c^{n}$. Only existence of such a $\rho$ is asserted; no canonicity or uniqueness.
--
--   This is the standard comparison of Mumford theta groups under passage to tensor powers: the theta group of $M$ maps to that of $M^{\otimes n}$ over the same translation points, with central scalars raised to the $n$th power. It feeds the computation of values of the level pairing obtained from commutators of theta-group elements along an isomorphism between a tensor power and a tensor product of tensor powers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tpow_pt_eq_and_isScalarElt_pow.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.thetaGroup.exists_monoidHom_tpow_pt_eq_and_isScalarElt_pow
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (M : A.Modules) (n : ℕ) (hn : 1 ≤ n) :
    ∃ ρ : thetaGroup f L hc M →* thetaGroup f L hc (Scheme.Modules.tpow M n),
      (∀ g : thetaGroup f L hc M, thetaGroup.pt f L hc (Scheme.Modules.tpow M n) (ρ g) = thetaGroup.pt f L hc M g) ∧
      (∀ (g : thetaGroup f L hc M) (c : k), thetaGroup.IsScalarElt f L hc M g c →
        thetaGroup.IsScalarElt f L hc (Scheme.Modules.tpow M n) (ρ g) (c ^ n)) := by sorry
