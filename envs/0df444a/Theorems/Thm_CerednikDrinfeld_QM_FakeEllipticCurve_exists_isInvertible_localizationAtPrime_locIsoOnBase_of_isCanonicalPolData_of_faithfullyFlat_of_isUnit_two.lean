-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_localizationAtPrime_locIsoOnBase_of_isCanonicalPolData_of_faithfullyFlat_of_isUnit_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_localizationAtPrime_locIsoOnBase_of_isCanonicalPolData_of_faithfullyFlat_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/2ea94678-57a5-5d1d-b339-d90fe568c1b4
-- title:
--   Descent of the canonical polarisation module to S_𝔭
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ is indefinite ($0<a$ or $0<b$) and, for each height-one prime $v$ of $\mathcal O_{\mathbb Q}$, the completion $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is an order maximal among orders, let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq')\cdot 1$, and let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu\,\mathrm{star}(x) = \bar x\,\mu$ for all $x$. Let $N \in \mathbb N$, let $S$ be a commutative ring in which $2$ is a unit, let $E$ be a `FakeEllipticCurve` for $(\Lambda,N,S)$ with structure morphism $f$ and relative group law $E.L$, let $\mathfrak p \in \operatorname{Spec} S$, and let $W$ be a commutative ring that is an algebra over both $S$ and $S_{\mathfrak p}$ compatibly, faithfully flat over $S_{\mathfrak p}$. Write $A_W$, $A_{\mathfrak p}$ for the base changes of $f$ along $S \to W$, $S \to S_{\mathfrak p}$ (second projections of the respective pullbacks), and call a relative group law on such a base change compatible when the first projection to $A$ carries its multiplication to that of $E.L$ over the composed base map. Assume that every compatible relative group law on $A_W$ admits a module on the pullback which is a canonical polarisation datum in the sense of `IsCanonicalPolData` for it, the base-changed $\Lambda$-action and $\mathrm{star}$ (invertible, symmetric, with Mumford kernel exactly the $2$-torsion, with a square-root decomposition of the Mumford bundle with trivial kernel after some faithfully flat base extension, with positive $h^0$ on every geometric fibre, and Rosati-compatible). Then for every compatible relative group law $L_{\mathfrak p}$ on $A_{\mathfrak p}$ there exist an invertible module $\mathcal L_{\mathfrak p}$ on the pullback over $S_{\mathfrak p}$, a compatible relative group law $L_W$ on $A_W$, and a module $\mathcal L_W$ which is a canonical polarisation datum for $L_W$, the base-changed $\Lambda$-action and $\mathrm{star}$, such that for every morphism $\rho$ of the pullback over $W$ to the pullback over $S_{\mathfrak p}$ commuting with the first projections and with the second projections up to the base map $S_{\mathfrak p}\to W$, the modules $\rho^{*}\mathcal L_{\mathfrak p}$ and $\mathcal L_W$ are isomorphic locally on the base $\operatorname{Spec} W$: every point of $\operatorname{Spec} W$ has an open neighbourhood $U$ over whose preimage the two restrictions are isomorphic.
--
--   This is the descent step in the construction of canonical polarisation data for fake elliptic curves: a canonical datum known to exist over a ring faithfully flat over the local ring $S_{\mathfrak p}$ yields an invertible module over $S_{\mathfrak p}$ whose pullback recovers it locally on the base. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isCanonicalPolData_localizationAtPrime_of_faithfullyFlat_of_isUnit_two`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isCanonicalPolData_localizationAtPrime_of_faithfullyFlat_of_isUnit_two) to produce a canonical polarisation datum over $S_{\mathfrak p}$ itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_localizationAtPrime_locIsoOnBase_of_isCanonicalPolData_of_faithfullyFlat_of_isUnit_two.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_localizationAtPrime_locIsoOnBase_of_isCanonicalPolData_of_faithfullyFlat_of_isUnit_two
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
    ∀ (L𝔭 : RelativeGroupLaw (Localization.AtPrime 𝔭.asIdeal) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)))
          (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
          (L𝔭.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
            (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))
              ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
      ∃ 𝓛𝔭 : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))).Modules,
        Scheme.Modules.IsInvertible 𝓛𝔭 ∧
        ∃ (LW : RelativeGroupLaw W (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of W))
          (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
          (LW.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))) =
            (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S W)))
              ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) ∧
          ∃ 𝓛W : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))).Modules,
            CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) LW
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓛W ∧
            ∀ (ρ : pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
              (hρ₁ : ρ ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
              (hρ₂ : ρ ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
                pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))) ≫ Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime 𝔭.asIdeal) W))),
              LocIsoOnBase (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
                ((Scheme.Modules.pullback ρ).obj 𝓛𝔭) 𝓛W := by sorry
