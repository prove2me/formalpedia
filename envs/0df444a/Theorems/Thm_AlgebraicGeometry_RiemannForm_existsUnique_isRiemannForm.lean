-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_existsUnique_isRiemannForm
-- name    : AlgebraicGeometry.RiemannForm.existsUnique_isRiemannForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/22eca238-e874-59dc-99a7-41846455f6be
-- title:
--   Existence and uniqueness of the ℓ-adic Riemann form
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law on $f$: a group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} k$, with multiplication natural in $T$. Assume $L$ is commutative ($hc$), and that $f$ satisfies the property bundle $\mathtt{AbelianSchemePropertyBundle}$: $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and a relative group law on $f$ exists. Let $\mathcal{L}$ be a module on $A$ which is invertible, i.e. locally on $A$ its pullback is isomorphic to the unit sheaf. Let $\ell$ be a prime with $\ell \neq 0$ in $k$, and let $\zeta : \mathbb{N} \to k$ satisfy: $\zeta_n$ is a primitive $\ell^n$-th root of unity for every $n$, and $\zeta_{n+1}^{\ell} = \zeta_n$. Then there is exactly one $\mathbb{Z}_{\ell}$-bilinear form $e$ on the Tate module of $k$-points of $L$ — the group of sequences $(x_n)$ of $k$-points with $\ell^n x_n = 0$ and $\ell x_{n+1} = x_n$ — with values in $\mathbb{Z}_{\ell}$, such that for all $n$ and all $a, b$ in that Tate module the scalar $\zeta_n^{\,\mathrm{appr}_n(e(a,b))}$ is a level-$\ell^n$ pairing value of $\mathcal{L}$ at the points $a_n, b_n$ in the sense of `IsLevelPairingValue`: translation by $a_n$ followed by multiplication by $\ell^n$ equals multiplication by $\ell^n$, and there is an isomorphism $\beta$ between the pullback along $[\ell^n]$ of the $b_n$-translate of $\mathcal{L}$ and the pullback along $[\ell^n]$ of $\mathcal{L}$ whose associated composite automorphism is multiplication by that scalar.
--
--   This is the existence and uniqueness of the $\ell$-adic Riemann form (Weil pairing attached to a line bundle) on an abelian variety over an algebraically closed field, packaged as a $\mathbb{Z}_{\ell}$-bilinear form on the Tate module compatible with a chosen coherent system of $\ell^n$-th roots of unity. It is used in the study of fake elliptic curves arising from quaternionic multiplication, where triviality of a kernel and Rosati-compatibility statements are deduced from properties of this pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_existsUnique_isRiemannForm.lean

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

theorem AlgebraicGeometry.RiemannForm.existsUnique_isRiemannForm
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (ζ : ℕ → k) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n) :
    ∃! e : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ],
      IsRiemannForm f L hc 𝓛 ℓ ζ e := by sorry
