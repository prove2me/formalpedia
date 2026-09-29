-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_not_mem_isCanonicalPolData_away_of_faithfullyFlat_symmetricSqrt_atPrime
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_not_mem_isCanonicalPolData_away_of_faithfullyFlat_symmetricSqrt_atPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/b4b2c75f-614d-5358-bdf1-e8424ad6602c
-- title:
--   Spreading a canonical polarisation datum out to a basic open
-- statement:
--   Let $q\neq q'$ be primes and let $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $0<a$ or $0<b$, and for every finite place $v$ of $\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ lies over $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a maximal order (a finitely generated $\mathbb{Z}$-submodule containing $1$, closed under multiplication and spanning the algebra over $\mathbb{Q}$, maximal among such), let $\mu\in\Lambda$ satisfy $\mu^2=-qq'$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\cdot\mathrm{star}(x)=\bar{x}\mu$ for all $x\in\Lambda$. Let $N\in\mathbb{N}$, let $S$ be a noetherian commutative ring in which $2$ is a unit, let $E$ be a fake elliptic curve of level $N$ over $S$ with structure morphism $E.f:A\to\operatorname{Spec} S$ and $\Lambda$-action $E.\mathrm{act}$, and let $\mathfrak{p}$ be a prime of $S$. Assume there is a ring $W$ that is an algebra over both $S$ and $S_{\mathfrak{p}}$ compatibly and is faithfully flat over $S_{\mathfrak{p}}$, with the following property: for every relative group law $L'$ on $A_W\to\operatorname{Spec} W$ for which the projection $A_W\to A$ carries $L'$-multiplication of points to $E.L$-multiplication, there is a module $\mathcal{L}'$ on $A_W$ with `IsCanonicalPolData` for $(A_W\to\operatorname{Spec} W, L')$, the pulled-back $\Lambda$-action and $\mathrm{star}$ — that is, $\mathcal{L}'$ is invertible, symmetric and positive on geometric fibres, the kernel of its Mumford bundle is exactly the $2$-torsion, it is Rosati-compatible with the $\Lambda$-action and $\mathrm{star}$, and after some faithfully flat base change it acquires a principal square root — and, in addition, an invertible module $\mathcal{L}_0$ on $A_W$ with trivial kernel, symmetric, such that $\mathcal{L}'$ is locally over the base isomorphic to $\mathcal{L}_0\otimes[-1]^{*}\mathcal{L}_0$. Then there exists $g\in S\setminus\mathfrak{p}$ such that for every relative group law $L'$ on $A_{S_g}\to\operatorname{Spec} S_g$ compatible with $E.L$ in the same sense, there is a module $\mathcal{L}'$ on $A_{S_g}$ satisfying `IsCanonicalPolData` for $(A_{S_g}\to\operatorname{Spec} S_g, L')$, the pulled-back $\Lambda$-action and $\mathrm{star}$.
--
--   This is the spreading-out step in the construction of the canonical polarisation on a fake elliptic curve: canonical polarisation data available over a faithfully flat cover of the local ring at $\mathfrak{p}$, together with a symmetric principal square root there, are propagated to a basic open neighbourhood of $\mathfrak{p}$ in $\operatorname{Spec} S$. It feeds the statement that produces, from such local input at every maximal ideal, a faithfully flat base change carrying a canonical polarisation datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_not_mem_isCanonicalPolData_away_of_faithfullyFlat_symmetricSqrt_atPrime.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_not_mem_isCanonicalPolData_away_of_faithfullyFlat_symmetricSqrt_atPrime
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] [IsNoetherianRing S] (h2 : IsUnit (2 : S)) (E : FakeEllipticCurve Λ N S)
    (𝔭 : PrimeSpectrum S)
    (h𝔭 : ∃ (W : Type) (_ : CommRing W) (_ : Algebra S W) (_ : Algebra (Localization.AtPrime 𝔭.asIdeal) W)
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
    ∃ g : S, g ∉ 𝔭.asIdeal ∧
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
            star 𝓛' := by sorry
