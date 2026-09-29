-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_not_mem_isCanonicalPolData_away_of_isCanonicalPolData_atPrime_of_symmetricSqrt
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_not_mem_isCanonicalPolData_away_of_isCanonicalPolData_atPrime_of_symmetricSqrt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/8a4f1184-18da-5af3-8292-e230877f06b5
-- title:
--   Spreading canonical polarisation data from a prime to a basic open
-- statement:
--   Fix distinct primes $q,q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for each height-one prime $v$ of the integers of $\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ that is an order maximal among orders, $\mu\in\Lambda$ with $\mu^{2}=-(qq')\cdot 1$, and $star:\Lambda\to\Lambda$ a map with $\mu\,star(x)=\bar{x}\mu$ for all $x\in\Lambda$. Let $N\in\mathbb{N}$, let $S$ be a noetherian commutative ring in which $2$ is a unit, let $E$ be a fake elliptic curve over $S$ of level $N$ with $\Lambda$-action (abelian scheme $f\colon A\to\operatorname{Spec} S$ with relative group law $E.L$, two-dimensional fibres and an action `E.act` of $\Lambda$ over $S$), and let $\mathfrak p$ be a prime of $S$. Assume: (i) there is a ring $W$, an algebra over both $S$ and $S_{\mathfrak p}$ in a scalar tower, faithfully flat over $S_{\mathfrak p}$, such that every relative group law $L'$ on $A_W$ whose multiplication is compatible with $E.L$ under the first projection admits a module $\mathcal L'$ on $A_W$ satisfying `IsCanonicalPolData` for the pulled-back $\Lambda$-action and $star$ (invertibility, symmetry, `KernelIsTwoTorsion`, existence of a principal square root after a faithfully flat base change, positivity of the geometric fibre $H^0$ rank, and `RosatiCompatible`), together with an invertible module $\mathcal L_0$ on $A_W$ with trivial kernel, symmetric, and with $\mathcal L'$ locally on the base isomorphic to $\mathcal L_0\otimes(-1)^{*}\mathcal L_0$; and (ii) the same existence of such a canonical polarisation datum $\mathcal L'$ (without the square root) for every compatible group law on $A_{S_{\mathfrak p}}$. Then there exists $g\in S$, $g\notin\mathfrak p$, such that for every compatible relative group law $L'$ on $A_{S_g}$ over the localisation away from $g$ there is a module $\mathcal L'$ on $A_{S_g}$ satisfying `IsCanonicalPolData` for the pulled-back $\Lambda$-action and $star$.
--
--   This is the spreading-out (limit) step in the construction of the canonical polarisation on a fake elliptic curve: a canonical polarisation datum known over the local ring at $\mathfrak p$, with a symmetric principal square root available over a faithfully flat cover, already exists over a basic open neighbourhood of $\mathfrak p$. It feeds the variant in which the square-root hypothesis itself is imposed at $\mathfrak p$, and is assembled from separate spreading results for the two-torsion kernel condition, the square root, the fibrewise positivity and Rosati compatibility.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_not_mem_isCanonicalPolData_away_of_isCanonicalPolData_atPrime_of_symmetricSqrt.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_not_mem_isCanonicalPolData_away_of_isCanonicalPolData_atPrime_of_symmetricSqrt
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
                (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L')).obj 𝓛₀))
    (hdat𝔭 : ∀ (L' : RelativeGroupLaw (Localization.AtPrime 𝔭.asIdeal) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
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
            star 𝓛') :
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
