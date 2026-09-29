-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_pullback_iso_of_forall_thickening
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_pullback_iso_of_forall_thickening
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/db634f36-75f5-56b1-9058-5092bd1b428c
-- title:
--   Algebraisation of compatible invertible modules on adic thickenings
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, and let $a,b\in\mathbb{Q}$ satisfy `IsIndefiniteRamifiedExactlyAt`: either $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible precisely when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order and is maximal among orders containing it, let $\mu\in\Lambda$ satisfy $\mu^{2}=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\,\mathrm{star}(x)=\bar{x}\mu$ for all $x\in\Lambda$. Let $N\in\mathbb{N}$, let $S$ be a commutative ring and $E$ a `FakeEllipticCurve` for $\Lambda$, $N$ over $S$, with structure morphism $E.f$ to $\operatorname{Spec} S$. Let $R$ be a noetherian local $S$-algebra, complete and separated for the adic topology of its maximal ideal $\mathfrak{m}$. Write $A_R$ for the fibre product of $E.f$ with $\operatorname{Spec}$ of $S\to R$, and $A_k$ for the fibre product with $\operatorname{Spec}$ of $S\to R/\mathfrak{m}^{k+1}$. Given morphisms $j_k:A_k\to A_R$ commuting with the first projections and compatible with the second projections through $\operatorname{Spec}(R\to R/\mathfrak{m}^{k+1})$, morphisms $t_k:A_k\to A_{k+1}$ commuting with the first projections and satisfying $j_k=j_{k+1}\circ t_k$, and modules $\mathcal{L}_k$ on $A_k$ that are invertible (each point has an open neighbourhood $U$ on which the restriction along $U.\iota$ is isomorphic to the unit module) with isomorphisms $t_k^{*}\mathcal{L}_{k+1}\cong\mathcal{L}_k$, the conclusion is that there exists an invertible module $\mathcal{L}$ on $A_R$ together with isomorphisms $j_k^{*}\mathcal{L}\cong\mathcal{L}_k$ for every $k$.
--
--   This is the Grothendieck existence (algebraisation) statement for line bundles on the abelian surface underlying a fake elliptic curve, formally completed along the maximal ideal of a complete noetherian local base. It feeds the construction of polarisation data over such bases and the passage from tower-compatible bundles to a single bundle on $A_R$ in the Čerednik–Drinfel'd part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_pullback_iso_of_forall_thickening.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open AlgebraicGeometry

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_pullback_iso_of_forall_thickening
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Algebra S R]

    (j : ∀ k : ℕ, pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))
    (hj₁ : ∀ k, j k ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))
    (hj₂ : ∀ k, j k ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
      pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1)))))
    (t : ∀ k : ℕ, pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1 + 1))))))
    (ht₁ : ∀ k, t k ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1 + 1))))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))
    (ht : ∀ k, t k ≫ j (k + 1) = j k)

    (𝓛k : ∀ k : ℕ, (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))))).Modules)
    (hinv : ∀ k, Scheme.Modules.IsInvertible (𝓛k k))
    (hcompat : ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback (t k)).obj (𝓛k (k + 1)) ≅ 𝓛k k)) :
    ∃ 𝓛 : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))).Modules,
      Scheme.Modules.IsInvertible 𝓛 ∧ ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback (j k)).obj 𝓛 ≅ 𝓛k k) := by sorry
