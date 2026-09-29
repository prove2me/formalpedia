-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_kernelTrivial_isSymmetric_isCanonicalPolData_tensor_pullback_negMor_of_isAdicComplete_of_isUnit_two_of_charP
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernelTrivial_isSymmetric_isCanonicalPolData_tensor_pullback_negMor_of_isAdicComplete_of_isUnit_two_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/8962e8d7-1f3a-543e-8855-8a39097fe5ff
-- title:
--   Symmetric principal root on a fake elliptic curve over complete local R
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a maximal order (an order maximal under inclusion among orders), $\mu \in \Lambda$ with $\mu^2 = -qq'$, and $\mathrm{star} : \Lambda \to \Lambda$ a map with $\mu \cdot \mathrm{star}(x) = \bar{x}\mu$ for all $x$. Let $E$ be a fake elliptic curve of level $N$ over a commutative ring $S$: a scheme $A$ with a structure morphism $f : A \to \operatorname{Spec} S$, a commutative relative group law $L$, an abelian-scheme property bundle, fibres of topological Krull dimension $2$, an action `act` of $\Lambda$ by endomorphisms over $\operatorname{Spec} S$ that are group-law homomorphisms and satisfy the trace condition, together with the remaining level-$N$ and curve data. The assertion is that for every Noetherian local $S$-algebra $R$, complete for its maximal-ideal-adic topology, with algebraically closed residue field of characteristic a prime $p$, in which $2$ is a unit, and for every relative group law $L'$ on the base change $\operatorname{pr}_2 : A \times_{\operatorname{Spec} S} \operatorname{Spec} R \to \operatorname{Spec} R$ whose multiplication is compatible with that of $E.L$ under the first projection (for all $T$, all $t' : T \to \operatorname{Spec} R$ and all points $P,Q$ over $t'$, the first projection of $L'.\mathrm{mul}\,t'\,P\,Q$ is $E.L.\mathrm{mul}$ applied to the projections of $P$ and $Q$), there exists a module $\mathcal{L}_0$ on $A \times_{\operatorname{Spec} S} \operatorname{Spec} R$ which is invertible (locally on the scheme isomorphic to the unit module), has trivial kernel in the sense of `KernelTrivial` (any point $x$ over any affine base change whose associated Mumford bundle is locally on the base trivial equals the identity section), is symmetric, i.e. its pullback along the inversion morphism $\mathrm{negMor}$ of $L'$ is locally on $\operatorname{Spec} R$ isomorphic to it, and such that $\mathcal{L}_0 \otimes [-1]^{*}\mathcal{L}_0$ satisfies `IsCanonicalPolData` for $L'$, for the $\Lambda$-action obtained from `E.act` by base change, and for $\mathrm{star}$ — that is, it is invertible, symmetric, its kernel is two-torsion, it admits a principal square root after a faithfully flat base change, its geometric fibre $h^0$ ranks are positive, and it is Rosati-compatible with the $\Lambda$-action and $\mathrm{star}$.
--
--   This produces, over a complete local Noetherian base with algebraically closed residue field in which $2$ is invertible, the symmetric principal root $\mathcal{L}_0$ of a canonical polarisation of a fake elliptic curve, the line bundle underlying the canonical polarisation datum used in the Čerednik–Drinfeld description of Shimura curves. It is invoked in the construction of a faithfully flat base change over which a canonical polarisation datum exists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_kernelTrivial_isSymmetric_isCanonicalPolData_tensor_pullback_negMor_of_isAdicComplete_of_isUnit_two_of_charP.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernelTrivial_isSymmetric_isCanonicalPolData_tensor_pullback_negMor_of_isAdicComplete_of_isUnit_two_of_charP
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S) :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsAlgClosed (IsLocalRing.ResidueField R)] [Algebra S R],
      IsUnit (2 : R) →
      ∀ (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p],

      ∀ (L' : RelativeGroupLaw R (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L' 𝓛₀ ∧
          IsSymmetric (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L' 𝓛₀ ∧
          CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L'
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L')).obj 𝓛₀) := by sorry
