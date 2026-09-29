-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_isLevelPairingValue_one_of_forall_dvd
-- name    : AlgebraicGeometry.RiemannForm.isLevelPairingValue_one_of_forall_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/99de6c75-eb64-5abb-a95c-ad5dd4d9badc
-- title:
--   Level-ℓ pairing is trivial when ℓ divides the Riemann form
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a morphism of schemes, and let $L$ be a relative group law on $f$, i.e. a group structure on the sets $\mathrm{SchemeHomOver}\,t\,f$ of sections of $f$ over each $k$-scheme $t : T \to \operatorname{Spec} k$, natural in $T$, assumed commutative ($hc$). Assume `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, its fibres are connected, and a relative group law exists. Let $\mathcal L$ be a module on $A$ which is invertible (locally isomorphic to the unit sheaf), let $g$ be a natural number such that every fibre $f^{-1}(s)$ has topological Krull dimension $g$, let $\ell$ be a prime with $\ell \neq 0$ in $k$, and let $\zeta : \mathbb N \to k$ be such that each $\zeta_n$ is a primitive $\ell^n$-th root of unity and $\zeta_{n+1}^{\ell} = \zeta_n$. Let $e$ be a $\mathbb Z_\ell$-bilinear form on the Tate module $T_\ell = \{x : \mathbb N \to L.\mathrm{AlgPoints}\,hc\,k \mid \ell^n x_n = 0,\ \ell x_{n+1} = x_n\}$ of $k$-points, and assume $e$ is a Riemann form for $\mathcal L$: for all $n$ and all $a, b \in T_\ell$, the level-$\ell^n$ pairing of $a_n$ and $b_n$ takes the value $\zeta_n^{(e\,a\,b).\mathrm{appr}\,n}$. Assume further that $\ell \mid e\,a\,b$ in $\mathbb Z_\ell$ for all $a, b$, and let $P, Q$ be $k$-points with $\ell P = \ell Q = 0$. Then the level-$\ell$ pairing of $P$ and $Q$ has value $1$: translation by $P$ commutes with the multiplication-by-$\ell$ morphism $L.\mathrm{schemeNsmul}\,\ell$, and there is an isomorphism $\beta$ between the pullback along $L.\mathrm{schemeNsmul}\,\ell$ of the translate of $\mathcal L$ by $Q$ and the pullback of $\mathcal L$ itself, such that the resulting automorphism built from $\beta$ and the two transport isomorphisms acts as multiplication by the constant $1 \in k$.
--
--   This is the first step in the standard argument that $\ell$-divisibility of the Riemann form of a line bundle forces the $\ell$-torsion to lie in the kernel of the associated polarisation: divisibility of $e$ by $\ell$ makes the level-$\ell$ commutator pairing identically trivial on $A[\ell](k)$. It feeds the construction of an isomorphism exhibiting $\mathcal L$ as an $\ell$-th tensor power twisted by a further bundle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_isLevelPairingValue_one_of_forall_dvd.lean

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

theorem AlgebraicGeometry.RiemannForm.isLevelPairingValue_one_of_forall_dvd
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (ζ : ℕ → k) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n)
    (e : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he : IsRiemannForm f L hc 𝓛 ℓ ζ e)
    (hdiv : ∀ a b : TateModule ℓ (L.AlgPoints hc k), (ℓ : ℤ_[ℓ]) ∣ e a b)
    (P Q : L.AlgPoints hc k) (hP : ℓ • P = 0) (hQ : ℓ • Q = 0) :
    IsLevelPairingValue f L 𝓛 ℓ (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint Q) 1 := by sorry
