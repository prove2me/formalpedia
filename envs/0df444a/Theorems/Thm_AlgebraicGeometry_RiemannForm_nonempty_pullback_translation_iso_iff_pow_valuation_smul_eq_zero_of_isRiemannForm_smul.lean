-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_nonempty_pullback_translation_iso_iff_pow_valuation_smul_eq_zero_of_isRiemannForm_smul
-- name    : AlgebraicGeometry.RiemannForm.nonempty_pullback_translation_iso_iff_pow_valuation_smul_eq_zero_of_isRiemannForm_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/ef749d4a-1806-5716-8ece-6e081f97c4d9
-- title:
--   Stabiliser of a line bundle with scalar Riemann form
-- statement:
--   Let $k$ be an algebraically closed field, $f : A \to \operatorname{Spec} k$ a morphism of schemes, and $L$ a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections over arbitrary $k$-schemes $t : T \to \operatorname{Spec} k$, assumed commutative (`hc`); assume `AbelianSchemePropertyBundle k f`, i.e. $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal M$ be a module on $A$ that is invertible, i.e. locally on $A$ its pullback is isomorphic to the unit module, let $g$ be a natural number such that every fibre $f^{-1}(s)$ has topological Krull dimension $g$, and let $\ell$ be a prime with $\ell \neq 0$ in $k$. Let $\zeta : \mathbb N \to k$ be a compatible system of primitive roots of unity, $\zeta_n$ primitive of order $\ell^n$ with $\zeta_{n+1}^{\ell} = \zeta_n$. Let $e_0$ be a $\mathbb Z_\ell$-bilinear form on the Tate module $T_\ell = \{(x_n) \mid \ell^n x_n = 0,\ \ell x_{n+1} = x_n\}$ of the group $L.\mathrm{AlgPoints}\ hc\ k$ of $k$-points, assumed a perfect pair, and let $u \in \mathbb Z_\ell$, $u \neq 0$, be such that $u \cdot e_0$ is a Riemann form for $\mathcal M$: for all $n$ and all $a, b \in T_\ell$, the level-$\ell^n$ pairing value of $\mathcal M$ at the points $a_n$, $b_n$ equals $\zeta_n^{((u\cdot e_0)(a,b)).\mathrm{appr}\,n}$, where for $x, y \in A(k)$ killed by $\ell^n$ the assertion that $c \in k$ is the level-$\ell^n$ pairing value means that translation by $x$ commutes with multiplication by $\ell^n$ and that for some isomorphism $\beta$ between the pullbacks along $[\ell^n]$ of $T_y^*\mathcal M$ and of $\mathcal M$ the resulting automorphism is multiplication by the constant $c$. Then for every $n$ and every $Q \in A(k)$ with $\ell^n Q = 0$, the pullback of $\mathcal M$ along translation by $Q$ is isomorphic to $\mathcal M$ if and only if $\ell^{v_\ell(u)} Q = 0$.
--
--   This identifies the $\ell$-power torsion of the stabiliser $K(\mathcal M)$ of an invertible module whose $\ell$-adic Riemann form is a scalar multiple of a perfect pairing, the case of Mumford's description of $K(L)$ in terms of the cokernel of the form on the Tate module that the uniqueness-of-polarisation argument requires. It feeds the computation of the Euler characteristic of such a module in [`AlgebraicGeometry.RiemannForm.eulerChar_ne_zero_and_pow_dvd_eulerChar_of_isRiemannForm_smul_of_isPerfPair`](thm.html#AlgebraicGeometry.RiemannForm.eulerChar_ne_zero_and_pow_dvd_eulerChar_of_isRiemannForm_smul_of_isPerfPair).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_nonempty_pullback_translation_iso_iff_pow_valuation_smul_eq_zero_of_isRiemannForm_smul.lean

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

theorem AlgebraicGeometry.RiemannForm.nonempty_pullback_translation_iso_iff_pow_valuation_smul_eq_zero_of_isRiemannForm_smul
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (ζ : ℕ → k) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n)
    (e₀ : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (h₀ : e₀.IsPerfPair) (u : ℤ_[ℓ]) (hu : u ≠ 0)
    (he : IsRiemannForm f L hc 𝓜 ℓ ζ (u • e₀))
    (n : ℕ) (Q : L.AlgPoints hc k) (hQ : ℓ ^ n • Q = 0) :
    Nonempty ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓜 ≅ 𝓜) ↔
      ℓ ^ u.valuation • Q = 0 := by sorry
