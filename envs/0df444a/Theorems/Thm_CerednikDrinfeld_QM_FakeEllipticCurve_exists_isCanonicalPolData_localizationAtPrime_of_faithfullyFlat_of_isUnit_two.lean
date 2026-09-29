-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isCanonicalPolData_localizationAtPrime_of_faithfullyFlat_of_isUnit_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isCanonicalPolData_localizationAtPrime_of_faithfullyFlat_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/d93d381d-b643-5417-88de-99880ef6a5d5
-- title:
--   Descent of canonical polarisation data to S_𝔭
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`: $0<a$ or $0<b$, and for a finite place $v$ of $\mathbb{Q}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ lies over $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ that is an order maximal among orders containing it, let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq')\cdot 1$, and let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu\,\mathrm{star}(x) = \bar{x}\mu$ for all $x \in \Lambda$. Let $N$ be a natural number, $S$ a commutative ring in which $2$ is a unit, $E$ a `FakeEllipticCurve` for $\Lambda$ of level $N$ over $S$ (an abelian surface $f : A \to \operatorname{Spec} S$ with commutative relative group law $E.L$, a $\Lambda$-action by endomorphisms over $S$, and the remaining structure of that record), and $\mathfrak p$ a prime of $S$. Let $W$ be a commutative ring that is simultaneously an $S$-algebra and an $S_{\mathfrak p}$-algebra in a compatible way, and faithfully flat as an $S_{\mathfrak p}$-module. Assume: for every relative group law $L'$ on the second projection of $A \times_{\operatorname{Spec} S} \operatorname{Spec} W$ over $W$ whose multiplication is carried by the first projection to the multiplication of $E.L$, there is a module $\mathcal{L}'$ on that pullback satisfying `IsCanonicalPolData` for $L'$, the $\Lambda$-action obtained from $E$ by base change, and $\mathrm{star}$ — that is: $\mathcal{L}'$ is invertible; it is symmetric, in the sense that its pullback along the inversion morphism is, locally on the base, isomorphic to it; its Mumford-bundle kernel is exactly the $2$-torsion of $L'$, as a condition on points valued in affine schemes; after some faithfully flat base change $\mathcal{L}'$ becomes, locally on the base, a product $\mathcal{L}_0 \otimes (-1)^{*}\mathcal{L}_0$ with $\mathcal{L}_0$ invertible with trivial kernel; the rank of $H^0$ on every geometric fibre is positive; and the Mumford bundle is Rosati-compatible with the $\Lambda$-action and $\mathrm{star}$. The conclusion is the same existence statement with $W$ replaced by $S_{\mathfrak p} =$ `Localization.AtPrime 𝔭.asIdeal`: every compatible relative group law on $A \times_{\operatorname{Spec} S} \operatorname{Spec} S_{\mathfrak p}$ over $S_{\mathfrak p}$ admits a module satisfying `IsCanonicalPolData` for the base-changed $\Lambda$-action and $\mathrm{star}$.
--
--   This is the faithfully flat descent step for canonical polarisation data on a fake elliptic curve: data over a faithfully flat $S_{\mathfrak p}$-algebra $W$ are pushed down to the local ring $S_{\mathfrak p}$ itself. It feeds the construction of canonical polarisation data away from a bad locus, used in the Čerednik–Drinfel'd analysis of Shimura curves attached to the indefinite quaternion algebra ramified exactly at $q$ and $q'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isCanonicalPolData_localizationAtPrime_of_faithfullyFlat_of_isUnit_two.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isCanonicalPolData_localizationAtPrime_of_faithfullyFlat_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (h2 : IsUnit (2 : S)) (E : FakeEllipticCurve Λ N S) (𝔭 : PrimeSpectrum S)
    (W : Type) [CommRing W] [Algebra S W] [Algebra (Localization.AtPrime 𝔭.asIdeal) W]
    [IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) W] (hW : Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) W)
    (hdat : ∀ (L' : RelativeGroupLaw W (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of W))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S W))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛' : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))).Modules,
          CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L'
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓛') :
    ∀ (L' : RelativeGroupLaw (Localization.AtPrime 𝔭.asIdeal) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛' : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))).Modules,
          CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))) L'
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓛' := by sorry
