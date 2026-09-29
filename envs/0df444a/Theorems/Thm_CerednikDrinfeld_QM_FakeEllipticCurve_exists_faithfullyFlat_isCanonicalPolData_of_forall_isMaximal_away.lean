-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_faithfullyFlat_isCanonicalPolData_of_forall_isMaximal_away
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_faithfullyFlat_isCanonicalPolData_of_forall_isMaximal_away
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/af280670-b209-5195-bac6-8383322ed626
-- title:
--   Canonical polarisation data on basic opens give a faithfully flat cover
-- statement:
--   Fix primes $q \ne q'$ and rationals $a,b$ such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds for $\mathbb{H}[\mathbb{Q},a,b]$, i.e. $0<a$ or $0<b$, and for every finite place $v$ of $\mathbb{Q}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ lies over $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, $\mu \in \Lambda$ with $\mu^2 = -(qq')\cdot 1$, and $star : \Lambda \to \Lambda$ a map with $\mu\,(star\,x) = \bar{x}\,\mu$ for all $x$. Let $N$ be a natural number, $S$ a Noetherian commutative ring in which $2$ is a unit, and $E$ a `FakeEllipticCurve Λ N S`, with structure morphism $E.f : A \to \operatorname{Spec} S$, relative group law $E.L$ and $\Lambda$-action $E.act$ over $S$. The hypothesis is that for every point $\mathfrak{p}$ of $\operatorname{Spec} S$ whose ideal is maximal there is $g \notin \mathfrak{p}$ with the following property: every relative group law $L'$ on the base change of $E.f$ to the localisation $S_g$ whose multiplication is carried by the first projection to the multiplication of $E.L$ admits a module $\mathcal{L}'$ on the base-changed scheme satisfying `IsCanonicalPolData` for $L'$, the transported $\Lambda$-action and $star$ — that is: $\mathcal{L}'$ is invertible, symmetric (its pullback along the inversion morphism is isomorphic to it locally on the base), the locus where the associated Mumford bundle restricted along a section is trivial locally on the base is exactly the $2$-torsion, after some faithfully flat extension of the base every compatible group law admits an invertible module with trivial kernel whose Mumford-type square $\mathcal{L}_0 \otimes (-1)^*\mathcal{L}_0$ is locally on the base isomorphic to the pullback of $\mathcal{L}'$, the $H^0$-rank on every geometric fibre is positive, and Rosati compatibility holds for the action and $star$. The conclusion asserts the existence of a commutative ring $S'$ with an $S$-algebra structure, faithfully flat as an $S$-module, such that the same statement holds verbatim over $S'$: every relative group law on the base change of $E.f$ to $S'$ compatible with $E.L$ in the above sense admits a module satisfying `IsCanonicalPolData` for the transported $\Lambda$-action and $star$.
--
--   This is the spreading-out step in the construction of the canonical polarisation on a fake elliptic curve (an abelian surface with quaternionic multiplication) over a general base: data available on a Zariski neighbourhood of each closed point are assembled into data over a single faithfully flat base change. It is used by the corresponding statement in which the local datum over each basic open is itself obtained after a faithfully flat extension admitting a symmetric square root.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_faithfullyFlat_isCanonicalPolData_of_forall_isMaximal_away.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_faithfullyFlat_isCanonicalPolData_of_forall_isMaximal_away
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] [IsNoetherianRing S] (h2 : IsUnit (2 : S)) (E : FakeEllipticCurve Λ N S)
    (hcov : ∀ 𝔭 : PrimeSpectrum S, 𝔭.asIdeal.IsMaximal → ∃ g : S, g ∉ 𝔭.asIdeal ∧
      ∀ (L' : RelativeGroupLaw (Localization.Away g) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of (Localization.Away g)))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛' : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))).Modules,
          CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))) L'
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓛') :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S'),
      Module.FaithfullyFlat S S' ∧
      ∀ (L' : RelativeGroupLaw S' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of S'))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛' : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules,
          CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L'
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓛' := by sorry
