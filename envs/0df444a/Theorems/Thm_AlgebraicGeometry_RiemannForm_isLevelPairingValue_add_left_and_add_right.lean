-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_isLevelPairingValue_add_left_and_add_right
-- name    : AlgebraicGeometry.RiemannForm.isLevelPairingValue_add_left_and_add_right
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/eff8c3a0-0a02-5809-8f7a-8b50a1b9142c
-- title:
--   Bimultiplicativity of level-n pairing values on torsion points
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme with a morphism $f : A \to \operatorname{Spec} k$, let $L$ be a relative group law on $f$ (functorial multiplication, unit and inverse on sections $T \to A$ over $\operatorname{Spec} k$, compatible with base change) that is commutative, and let `hA` record that $f$ is smooth and proper, has connected fibres and admits a relative group law. Let $\mathcal{L}$ be a module on $A$ that is invertible, i.e. locally isomorphic to the unit sheaf, let $n$ be a natural number with $n \neq 0$ in $k$, and let $P, P', Q, Q'$ be $k$-points of $L$ (written additively) with $nP = nP' = nQ = nQ' = 0$. Let $c, c', d \in k$, and assume that $c$ is a level-$n$ pairing value at $(P, Q)$: there is an identity $T_P \circ [n] = [n]$ between the translation by $P$ composed with multiplication by $n$ and $[n]$, and an isomorphism $\beta : [n]^{*}T_Q^{*}\mathcal{L} \cong [n]^{*}\mathcal{L}$, such that the composite of $\beta^{-1}$, the inverse transport isomorphism along that identity for $T_Q^{*}\mathcal{L}$, the pullback of $\beta$ along $T_P$, and the transport isomorphism for $\mathcal{L}$, acts on every section over every open set as multiplication by the scalar coming from $c$. The conclusion is the conjunction of two implications: if $c'$ is a level-$n$ pairing value at $(P', Q)$ then $cc'$ is one at $(P + P', Q)$, and if $d$ is a level-$n$ pairing value at $(P, Q')$ then $cd$ is one at $(P, Q + Q')$.
--
--   This is the bimultiplicativity of the Weil pairing $e_n^{\mathcal{L}}$ attached to an invertible sheaf on an abelian variety, in the value-relation form used throughout the formalisation: values of the pairing multiply when either argument is added. It feeds the construction of a Riemann form ([`AlgebraicGeometry.RiemannForm.exists_isRiemannForm`](thm.html#AlgebraicGeometry.RiemannForm.exists_isRiemannForm)) and the statement that pairing values are $n$-th roots of unity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_isLevelPairingValue_add_left_and_add_right.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.isLevelPairingValue_add_left_and_add_right
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (n : ℕ) (hn : (n : k) ≠ 0) (P P' Q Q' : L.AlgPoints hc k)
    (hP : n • P = 0) (hP' : n • P' = 0) (hQ : n • Q = 0) (hQ' : n • Q' = 0) (c c' d : k)
    (h₁ : IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint Q) c) :
    (IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P') (RelativeGroupLaw.AlgPoints.toPoint Q) c' →
      IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint (P + P')) (RelativeGroupLaw.AlgPoints.toPoint Q) (c * c')) ∧
    (IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint Q') d →
      IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint (Q + Q')) (c * d)) := by sorry
