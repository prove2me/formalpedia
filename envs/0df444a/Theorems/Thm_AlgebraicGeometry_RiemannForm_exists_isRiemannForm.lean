-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_exists_isRiemannForm
-- name    : AlgebraicGeometry.RiemannForm.exists_isRiemannForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/31bf4158-fc72-5680-87fe-8a70b06ccdf3
-- title:
--   Existence of the ℓ-adic Riemann form of an invertible module
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law for $f$: a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} k$, with multiplication, unit and inverse satisfying associativity, the unit laws and left inversion, and compatible with base change $T' \to T$. Assume $L$ is commutative ($hc$), and that $f$ carries the property bundle $hA$ consisting of smoothness, properness, connectedness of all fibres of the underlying map, and the existence of a relative group law. Let $\mathcal{L}$ be a module on $A$ which is invertible, in the sense that every point has an open neighbourhood $U$ with $\mathcal{L}|_U$ isomorphic to the unit module of $U$. Let $\ell$ be a prime which is nonzero in $k$, and let $\zeta : \mathbb{N} \to k$ be such that each $\zeta_n$ is a primitive $\ell^n$-th root of unity and $\zeta_{n+1}^{\ell} = \zeta_n$. Write $T =$ [`TateModule ℓ (L.AlgPoints hc k)`](def/EllipticCurve_TateModule.html#L15) for the group of sequences $(x_n)$ of $k$-points of $A$ (the group, under $L$, of sections of $f$ over $\operatorname{Spec} k$) with $\ell^n x_n = 0$ and $\ell x_{n+1} = x_n$. The assertion is that there exists a $\mathbb{Z}_\ell$-bilinear map $e : T \times T \to \mathbb{Z}_\ell$ which is a Riemann form for $\mathcal{L}$ in the sense of `IsRiemannForm`: for all $n$ and all $a, b \in T$, the scalar $\zeta_n^{\,c}$, where $c$ is the $n$-th approximant of $e(a,b)$ in $\mathbb{Z}/\ell^n$, is a level-$\ell^n$ pairing value of the points $a_n, b_n$, i.e. translation by $a_n$ followed by multiplication by $\ell^n$ equals multiplication by $\ell^n$, and there is an isomorphism $\beta$ between the pullback under $[\ell^n]$ of the translate of $\mathcal{L}$ by $b_n$ and the pullback under $[\ell^n]$ of $\mathcal{L}$ such that the composite automorphism assembled from $\beta$, its translate by $a_n$ and the transport isomorphisms along that identity of morphisms is multiplication by the constant $\zeta_n^{\,c}$.
--
--   This is the existence half of the construction of the $\ell$-adic Riemann form $e^{\mathcal{L}}$ attached to an invertible module on an abelian variety over an algebraically closed field, the $\ell$-adic limit of the level-$\ell^n$ commutator pairings on $\ell^n$-torsion. It is combined with uniqueness in [`AlgebraicGeometry.RiemannForm.existsUnique_isRiemannForm`](thm.html#AlgebraicGeometry.RiemannForm.existsUnique_isRiemannForm); the proof cites the well-definedness, root-of-unity, biadditivity and level-compatibility properties of the level pairing values.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_exists_isRiemannForm.lean

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

theorem AlgebraicGeometry.RiemannForm.exists_isRiemannForm
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (ζ : ℕ → k) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n) :
    ∃ e : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ],
      IsRiemannForm f L hc 𝓛 ℓ ζ e := by sorry
