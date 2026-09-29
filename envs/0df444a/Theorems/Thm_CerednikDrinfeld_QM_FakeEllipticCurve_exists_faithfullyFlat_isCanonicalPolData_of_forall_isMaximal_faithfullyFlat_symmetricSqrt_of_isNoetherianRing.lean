-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_faithfullyFlat_isCanonicalPolData_of_forall_isMaximal_faithfullyFlat_symmetricSqrt_of_isNoetherianRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_faithfullyFlat_isCanonicalPolData_of_forall_isMaximal_faithfullyFlat_symmetricSqrt_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/619c7144-d9c5-533b-9b50-c2834b0b312d
-- title:
--   Spreading canonical polarisation data from the closed points
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, at each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, its $v$-adic completion is a division algebra exactly when $q$ or $q'$ lies in $v$; let $\Lambda$ be a maximal order (an order maximal among orders), $\mu \in \Lambda$ with $\mu^2 = -(qq')\cdot 1$, and $star : \Lambda \to \Lambda$ a map with $\mu \cdot star(x) = \bar{x}\mu$ for all $x$. Let $N : \mathbb{N}$, let $S$ be a noetherian commutative ring in which $2$ is a unit, and let $E$ be a `FakeEllipticCurve` for $\Lambda$, $N$ over $S$, with structure morphism $E.f : A \to \operatorname{Spec} S$, relative group law $E.L$ and $\Lambda$-action $E.act$. Assume that for every maximal prime $\mathfrak{p}$ of $S$ there is a ring $W$, an $S$-algebra and $S_{\mathfrak{p}}$-algebra compatibly (scalar tower) with $W$ faithfully flat over $S_{\mathfrak{p}}$, such that every relative group law $L'$ on the base change $A_W \to \operatorname{Spec} W$ whose multiplication is carried by the first projection to that of $E.L$ admits a module $\mathcal{L}'$ on $A_W$ which is a canonical polarisation datum for $L'$, the action transported by $\operatorname{pullback.lift}$ and $star$ — that is, $\mathcal{L}'$ is invertible, symmetric under the inversion morphism, has kernel the $2$-torsion, has positive geometric fibre $H^0$ rank over algebraically closed fields, is Rosati-compatible with the action and $star$, and admits a principal square root after a faithfully flat base change — and which moreover admits over $W$ itself an invertible $\mathcal{L}_0$ with trivial kernel, symmetric, with $\mathcal{L}'$ locally isomorphic over the base to $\mathcal{L}_0 \otimes (\text{neg})^{*}\mathcal{L}_0$. The conclusion: there exist a commutative ring $S'$ and an $S$-algebra structure on it with $S'$ faithfully flat over $S$ such that every relative group law on $A_{S'}$ compatible with $E.L$ in the same sense admits a module $\mathcal{L}'$ on $A_{S'}$ that is a canonical polarisation datum for it, the transported $\Lambda$-action and $star$. The extra symmetric square-root clause of the hypothesis is not asserted in the conclusion.
--
--   This is the globalisation step for canonical polarisations on fake elliptic curves: a hypothesis imposed at each closed point of $\operatorname{Spec} S$, with an auxiliary symmetric principal square root available over the local faithfully flat algebra, is converted into a single faithfully flat cover of $S$ carrying the canonical datum. It feeds the variant of the same statement whose hypothesis is phrased in terms of adically complete algebras of finite type in positive characteristic, in the Čerednik–Drinfeld part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_faithfullyFlat_isCanonicalPolData_of_forall_isMaximal_faithfullyFlat_symmetricSqrt_of_isNoetherianRing.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_faithfullyFlat_isCanonicalPolData_of_forall_isMaximal_faithfullyFlat_symmetricSqrt_of_isNoetherianRing
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] [IsNoetherianRing S] (h2 : IsUnit (2 : S)) (E : FakeEllipticCurve Λ N S)
    (hloc : ∀ 𝔭 : PrimeSpectrum S, 𝔭.asIdeal.IsMaximal →
      ∃ (W : Type) (_ : CommRing W) (_ : Algebra S W) (_ : Algebra (Localization.AtPrime 𝔭.asIdeal) W)
        (_ : IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) W),
        Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) W ∧
      ∀ (L' : RelativeGroupLaw W (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
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
            star 𝓛' ∧
          ∃ 𝓛₀ : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))).Modules,
            Scheme.Modules.IsInvertible 𝓛₀ ∧
            KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L' 𝓛₀ ∧
            IsSymmetric (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L' 𝓛₀ ∧
            LocIsoOnBase (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
              𝓛'
              (𝓛₀ ⊗ (Scheme.Modules.pullback
                (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L')).obj 𝓛₀)) :
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
