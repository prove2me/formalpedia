-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_isRiemannForm_unique
-- name    : AlgebraicGeometry.RiemannForm.isRiemannForm_unique
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/dc158563-47b5-57d3-b1e5-e457ab677536
-- title:
--   Uniqueness of the ℓ-adic Riemann form of a line bundle
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law on $f$: a group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} k$, natural in $T$, assumed commutative by the hypothesis $hc$. Assume the bundle $hA$ of properties of $f$: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and a relative group law on $f$ exists. Let $\mathcal{L}$ be a module sheaf on $A$ that is invertible, i.e. locally on $A$ its pullback is isomorphic to the unit sheaf. Let $\ell$ be a prime that is nonzero in $k$, and let $\zeta : \mathbb{N} \to k$ be such that each $\zeta_n$ is a primitive $\ell^n$-th root of unity and $\zeta_{n+1}^{\ell} = \zeta_n$. Let $e, e'$ be $\mathbb{Z}_\ell$-bilinear forms on the Tate module $T_\ell$, the group of sequences $(x_n)$ of $k$-points of $L$ with $\ell^n x_n = 0$ and $\ell x_{n+1} = x_n$, and suppose both are Riemann forms of $\mathcal{L}$ with respect to $\zeta$: for all $n$ and all $a, b \in T_\ell$, the scalar $\zeta_n^{(e\,a\,b).\mathrm{appr}\,n}$ is a level-$\ell^n$ pairing value of $\mathcal{L}$ at $(a_n, b_n)$, meaning that translation by $a_n$ commutes with multiplication by $\ell^n$ and that for some isomorphism $\beta$ between the pullback along $[\ell^n]$ of the translate of $\mathcal{L}$ by $b_n$ and the pullback along $[\ell^n]$ of $\mathcal{L}$, the resulting automorphism is multiplication by that constant. Then $e = e'$.
--
--   This is the uniqueness half of the statement that an invertible sheaf on an abelian variety determines at most one $\ell$-adic Riemann form, the pairing $e^{\mathcal{L}}$ assembled from the level-$\ell^n$ pairings. It is used to produce the Riemann form as a well-defined object (in the existence-and-uniqueness statement) and in the construction of fake elliptic curves in the Čerednik–Drinfel'd setting, where a pairing is identified by its level-wise values.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_isRiemannForm_unique.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.isRiemannForm_unique
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (ζ : ℕ → k) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n)
    (e : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he : IsRiemannForm f L hc 𝓛 ℓ ζ e)
    (e' : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he' : IsRiemannForm f L hc 𝓛 ℓ ζ e') :
    e = e' := by sorry
