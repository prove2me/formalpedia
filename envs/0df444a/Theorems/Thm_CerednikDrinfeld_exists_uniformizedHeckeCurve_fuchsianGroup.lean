-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_uniformizedHeckeCurve_fuchsianGroup
-- name    : CerednikDrinfeld.exists_uniformizedHeckeCurve_fuchsianGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/dcb08714-4cf2-58a8-9b30-a38d369e947c
-- title:
--   Complex uniformisation of the Shimura curve of an Eichler order
-- statement:
--   Let $q,q'$ be primes, $N$ a nonzero natural number, and $a,b$ rational numbers such that the quaternion algebra $B=\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the completion $B\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda,R$ be $\mathbb Z$-submodules of $B$ with $\Lambda$ a maximal order, $R$ an Eichler order of level $N$ (an intersection $\Lambda_1\cap\Lambda_2$ of two maximal orders of relative index $N$ in $\Lambda_1$), and $R\le\Lambda$; let $\iota:B\to M_2(\mathbb R)$ be an injective $\mathbb Q$-algebra homomorphism, and $\Gamma=$ `fuchsianGroup R ι`, the image of the unit group of $R$ under $\iota$ intersected with the kernel of the determinant. Then there exist a field $Fc$ with a $\mathbb C$-algebra structure making it a curve over $\mathbb C$ in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15) (principal divisors, finite residue field extensions of $\mathbb C$, and $\Omega_{Fc/\mathbb C}$ free of rank one), essentially of finite type over $\mathbb C$, and a [`ModularCurve.UniformizedHeckeCurve`](def/ModularCurve_UniformizedHeckeCurve.html#L14) structure $U$ for $(\Gamma,Fc)$ such that: the place map $U.\mathrm{pt}:\mathfrak h\to$ places of $Fc/\mathbb C$ is surjective; for every prime $\ell$ there is a finite set $S\subset B$ whose elements lie in $R$, have reduced norm $\mathrm{nrd}=\ell$ and satisfy $x\otimes 1\in\mathcal S_\ell$, where $\mathcal S_\ell$ is `levelHeckeUSet Λ R ℓ` if $\ell\mid N$ and `primeHeckeSet R ℓ` otherwise (finite-adelic unit conditions: $h$ and $\ell h^{-1}$ in the adelic box of $R$ while $h^{-1}$ and $\ell^{-1}h$ are not, together with, in the level case, $h$ not normalising $R$ and $R$ not contained in the $h$-conjugate of $\Lambda$), such that every $y\in R$ with $\mathrm{nrd}\,y=\ell$ and $y\otimes1\in\mathcal S_\ell$ is $u x$ for a unique $x\in S$ and some unit $u$ of $R$ of reduced norm $1$, and the multiset $U.\mathrm{heckePoints}\,\ell$, viewed in $M_2(\mathbb R)$, equals the image of $S$ under $\iota$. Moreover the realisation map of $U$ identifies $Fc$, on germs at each point of the upper half plane, with the $\Gamma$-invariant meromorphic functions: each $U.\mathrm{realize}\,x$ is meromorphic at every $\tau$, realisation is additive and multiplicative and sends scalars from $\mathbb C$ to constants on punctured neighbourhoods, it is injective on germs at all $\tau$, its values are $\Gamma$-invariant near each $\tau$, and every $\Gamma$-invariant meromorphic function on the upper half plane agrees near every $\tau$ with the realisation of some $x\in Fc$.
--
--   This is the complex uniformisation of the Shimura curve attached to an Eichler order $R$ in an indefinite rational quaternion division algebra, packaged together with its arithmetic Hecke correspondences and with the identification of the function field with the field of $\Gamma$-automorphic meromorphic functions. It is the analytic input for the construction of canonical models and is used by the Čerednik–Drinfeld statements on Hecke correspondences for quaternionic modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_uniformizedHeckeCurve_fuchsianGroup.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Topology Quaternion TensorProduct NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.exists_uniformizedHeckeCurve_fuchsianGroup
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {N : ℕ} [NeZero N]
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) :
    ∃ (Fc : Type) (_ : Field Fc) (_ : Algebra ℂ Fc) (_ : AlgebraicCurve.IsCurveOver ℂ Fc)
      (_ : Algebra.EssFiniteType ℂ Fc) (U : ModularCurve.UniformizedHeckeCurve (fuchsianGroup R ι) Fc),
      Function.Surjective U.pt ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ∃ S : Finset ℍ[ℚ, a, b],
        (∀ x ∈ S, x ∈ R ∧ nrd x = ℓ ∧
          ∃ h ∈ (if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
            (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = x ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∧
        (∀ y : ℍ[ℚ, a, b], y ∈ R → nrd y = ℓ →
          (∃ h ∈ (if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
            (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = y ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) →
          ∃! x, x ∈ S ∧ ∃ u : ℍ[ℚ, a, b], IsUnitOf R u ∧ nrd u = 1 ∧ u * x = y) ∧
        (U.heckePoints ℓ hℓ).map (fun g => (g : Matrix (Fin 2) (Fin 2) ℝ)) = S.val.map ι) ∧
      (∀ (x : Fc) (τ : UpperHalfPlane), MeromorphicAt (fun z : ℂ => U.realize x (UpperHalfPlane.ofComplex z)) (τ : ℂ)) ∧
      (∀ (x y : Fc) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U.realize (x + y) z = U.realize x z + U.realize y z) ∧
      (∀ (x y : Fc) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U.realize (x * y) z = U.realize x z * U.realize y z) ∧
      (∀ (c : ℂ) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U.realize (algebraMap ℂ Fc c) z = c) ∧
      (∀ x y : Fc, (∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U.realize x z = U.realize y z) → x = y) ∧
      (∀ x : Fc, ∀ γ ∈ fuchsianGroup R ι, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U.realize x (γ • z) = U.realize x z) ∧
      (∀ f : UpperHalfPlane → ℂ, (∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => f (UpperHalfPlane.ofComplex z)) (τ : ℂ)) →
        (∀ γ ∈ fuchsianGroup R ι, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, f (γ • z) = f z) →
        ∃ x : Fc, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U.realize x z = f z) := by sorry
