-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_mul_eq_one_of_isLevelPairingValue_of_isLevelPairingValue_swap
-- name    : AlgebraicGeometry.RiemannForm.mul_eq_one_of_isLevelPairingValue_of_isLevelPairingValue_swap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/11f7be9a-b27b-5613-8680-59dcd365dbe1
-- title:
--   Skew-symmetry of the level-n pairing values
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law on $f$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} k$, natural in $T$; assume $L$ is commutative (`hc`) and that $f$ satisfies `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, every fibre of $f$ is connected, and $f$ admits a relative group law. Let $\mathcal L$ be a module on $A$ that is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ on which the restriction of $\mathcal L$ is isomorphic to the unit module of $U$. Let $n$ be a natural number whose image in $k$ is nonzero, and let $P, Q$ be $k$-points of $A$ in the additive group $L.\mathrm{AlgPoints}$ with $n \cdot P = 0$ and $n \cdot Q = 0$. Let $c, c' \in k$ and suppose that `IsLevelPairingValue` holds for $(\mathcal L, n, P, Q, c)$ and for $(\mathcal L, n, Q, P, c')$; that is, in each case translation by the first point commutes with the multiplication-by-$n$ morphism $[n]$ (so that $T_x \circ [n] = [n]$), there is an isomorphism $\beta : [n]^{*}T_y^{*}\mathcal L \cong [n]^{*}\mathcal L$, and the resulting automorphism of $[n]^{*}\mathcal L$ obtained by composing $\beta^{-1}$, the inverse of the transport isomorphism for $T_x^{*}[n]^{*}T_y^{*}\mathcal L \cong [n]^{*}T_y^{*}\mathcal L$, the pullback of $\beta$ along $T_x$, and the transport isomorphism for $\mathcal L$, acts on all local sections as multiplication by the constant scalar $c$ (respectively $c'$) pulled back from $k$. Then $c\,c' = 1$.
--
--   This is the skew-symmetry of the Weil-type level-$n$ pairing attached to an invertible sheaf on an abelian scheme over an algebraically closed field: the value of $e_n^{\mathcal L}$ at $(P,Q)$ is inverse to its value at $(Q,P)$. It is used to derive `isRiemannForm_swap_eq_neg_and_self_eq_zero`, the alternating property of the associated Riemann form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_mul_eq_one_of_isLevelPairingValue_of_isLevelPairingValue_swap.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.mul_eq_one_of_isLevelPairingValue_of_isLevelPairingValue_swap
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (n : ℕ) (hn : (n : k) ≠ 0) (P Q : L.AlgPoints hc k) (hP : n • P = 0) (hQ : n • Q = 0) (c c' : k)
    (h₁ : IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint Q) c)
    (h₂ : IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint Q) (RelativeGroupLaw.AlgPoints.toPoint P) c') :
    c * c' = 1 := by sorry
