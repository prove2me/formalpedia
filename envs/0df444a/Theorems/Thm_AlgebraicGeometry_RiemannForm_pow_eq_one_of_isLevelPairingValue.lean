-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_pow_eq_one_of_isLevelPairingValue
-- name    : AlgebraicGeometry.RiemannForm.pow_eq_one_of_isLevelPairingValue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/a52f42fc-1385-558b-9b2f-f2aa7164e5d6
-- title:
--   Level-n pairing values are n-th roots of unity
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a scheme over $k$, let $L$ be a relative group law on $f$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} k$, natural in $T$), assume $L$ commutative, and assume the bundle `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal{L}$ be a module on $A$ which is invertible, i.e. every point of $A$ has an open neighbourhood $U$ on which the restriction of $\mathcal{L}$ is isomorphic to the unit sheaf of modules. Let $n$ be a natural number whose image in $k$ is nonzero, and let $P, Q$ be $k$-points of $A$ in the group $L.AlgPoints$ (the additive group of sections of $f$ over $\operatorname{Spec} k$) with $n \cdot P = n \cdot Q = 0$. Let $c \in k$ and suppose `IsLevelPairingValue` holds for $(\mathcal{L}, n, P, Q, c)$: translation by $P$ followed by the multiplication-by-$n$ morphism equals the multiplication-by-$n$ morphism, and there is an isomorphism $\beta$ between the pullback along multiplication by $n$ of the translate of $\mathcal{L}$ by $Q$ and the pullback along multiplication by $n$ of $\mathcal{L}$, for which the resulting commutator automorphism, assembled from $\beta$, its pullback along translation by $P$, and the two transport isomorphisms, acts on every local section as multiplication by the image of $c$ in the structure sheaf. Then $c^n = 1$.
--
--   This is the assertion that the level-$n$ Riemann (Weil) pairing on $n$-torsion points takes values in the group $\mu_n$ of $n$-th roots of unity. It feeds the construction of a Riemann form, [`AlgebraicGeometry.RiemannForm.exists_isRiemannForm`](thm.html#AlgebraicGeometry.RiemannForm.exists_isRiemannForm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_pow_eq_one_of_isLevelPairingValue.lean

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

theorem AlgebraicGeometry.RiemannForm.pow_eq_one_of_isLevelPairingValue
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (n : ℕ) (hn : (n : k) ≠ 0) (P Q : L.AlgPoints hc k) (hP : n • P = 0) (hQ : n • Q = 0) (c : k)
    (h : IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint Q) c) :
    c ^ n = 1 := by sorry
