-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_mem_stratum_iff_of_semilinear
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.mem_stratum_iff_of_semilinear
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/20dc46b6-5df6-5395-bff2-c2bcbb58d5d7
-- title:
--   Strata of Drinfeld data pull back along semilinear comparisons
-- statement:
--   Fix a prime $p$ and two commutative rings $B$, $B'$ that are $\mathbb{Z}_p$-algebras, together with a $\mathbb{Z}_p$-algebra homomorphism $f\colon B\to B'$. Let $Q$ and $Q'$ be Drinfeld data over $B$ and over $B'$ respectively, taken with $\mathcal{O}=\mathbb{Z}_p$, $K=\mathbb{Q}_p$ and uniformiser $\pi=p$; thus each consists of two families of full $\mathbb{Z}_p$-lattices $N_0(x)\le N_1(x)$ in $\mathbb{Q}_p^2$ indexed by the points $x$ of the prime spectrum, with $p\,N_1(x)\subseteq N_0(x)$, the membership loci of each vector being open, of two invertible modules $T_0$, $T_1$ over the base ring with linear maps $\Pi_0\colon T_0\to T_1$ and $\Pi_1\colon T_1\to T_0$ whose two composites are multiplication by $p$, and of comparison maps at every point between the base change of the lattices to the local ring and the stalks of $T_0$, $T_1$, compatible with the inclusion and with multiplication by $\pi$. Assume given maps $\tau_0\colon Q.T_0\to Q'.T_0$ and $\tau_1\colon Q.T_1\to Q'.T_1$, semilinear over the ring homomorphism underlying $f$, whose images span $Q'.T_0$ and $Q'.T_1$ over $B'$, and which intertwine the two $\Pi$ maps: $\tau_1(Q.\Pi_0 s)=Q'.\Pi_0(\tau_0 s)$ and $\tau_0(Q.\Pi_1 s)=Q'.\Pi_1(\tau_1 s)$. Then for every prime $x'$ of $B'$, writing $f^{-1}x'$ for the point of $\operatorname{Spec} B$ obtained by pulling $x'$ back along $f$, one has $x'\in Q'.\mathrm{stratum}_0$ if and only if $f^{-1}x'\in Q.\mathrm{stratum}_0$, and likewise $x'\in Q'.\mathrm{stratum}_1$ if and only if $f^{-1}x'\in Q.\mathrm{stratum}_1$.
--
--   This records that the two strata attached to a Drinfeld datum are compatible with base change of the module part of the datum, the typical case being $T'_i=B'\otimes_B T_i$ with $\Pi'_i=\Pi_i\otimes B'$, so that the stratification of the special fibre in the Čerednik–Drinfeld picture is determined pointwise and may be checked after any base change with spanning image. It is used in the verification that a rigidified Cartier quadruple is obtained by base change along such a morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_mem_stratum_iff_of_semilinear.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.mem_stratum_iff_of_semilinear
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [Algebra ℤ_[p] B] {B' : Type} [CommRing B'] [Algebra ℤ_[p] B']
    (f : B →ₐ[ℤ_[p]] B')
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B')
    (τ₀ : Q.T₀ →ₛₗ[(f : B →+* B')] Q'.T₀) (τ₁ : Q.T₁ →ₛₗ[(f : B →+* B')] Q'.T₁)
    (hτ₀ : Submodule.span B' (Set.range τ₀) = ⊤) (hτ₁ : Submodule.span B' (Set.range τ₁) = ⊤)
    (hPi₀ : ∀ s, τ₁ (Q.Pi₀ s) = Q'.Pi₀ (τ₀ s)) (hPi₁ : ∀ s, τ₀ (Q.Pi₁ s) = Q'.Pi₁ (τ₁ s))
    (x' : PrimeSpectrum B') :
    (x' ∈ Q'.stratum₀ ↔ DrinfeldDatum.pointUnder f x' ∈ Q.stratum₀) ∧
      (x' ∈ Q'.stratum₁ ↔ DrinfeldDatum.pointUnder f x' ∈ Q.stratum₁) := by sorry
