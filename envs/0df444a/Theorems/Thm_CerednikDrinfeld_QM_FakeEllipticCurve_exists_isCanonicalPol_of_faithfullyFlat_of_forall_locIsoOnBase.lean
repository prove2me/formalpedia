-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isCanonicalPol_of_faithfullyFlat_of_forall_locIsoOnBase
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isCanonicalPol_of_faithfullyFlat_of_forall_locIsoOnBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/655b4541-a19b-525d-9c26-05be303f4e95
-- title:
--   Descent of a canonical polarisation on a fake elliptic curve
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds for $\mathbb{H}[\mathbb{Q},a,b]$, i.e. $0<a$ or $0<b$, and for each height-one prime $v$ of $\mathcal{O}_\mathbb{Q}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_\mathbb{Q}\mathbb{Q}_v$ is a unit exactly when $v$ lies above $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is a maximal order (an order containing no strictly larger order), let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\cdot\mathrm{star}(x)=\bar{x}\mu$ for all $x\in\Lambda$. Let $N\in\mathbb{N}$, let $S$ be a commutative ring and let $E$ be a `FakeEllipticCurve Λ N S`, with structure morphism $E.f:E.A\to\operatorname{Spec} S$, relative group law $E.L$ and $\Lambda$-action $E.\mathrm{act}$. Three hypotheses are assumed. (hH0) For every commutative $S$-algebra $T$, the structural map from $T$ to the global sections of the base change $E.A\times_{\operatorname{Spec} S}\operatorname{Spec} T$ is bijective. (hloc) There is a faithfully flat $S$-algebra $S'$ such that for every relative group law $L'$ on the projection $E.A\times_{\operatorname{Spec} S}\operatorname{Spec} S'\to\operatorname{Spec} S'$ which is compatible with $E.L$ (for all $T$, all $t':T\to\operatorname{Spec} S'$ and all points $P,Q$ over $t'$, the first projection of $L'.\mathrm{mul}\,t'\,P\,Q$ is the $E.L$-product of the projections of $P$ and $Q$) there is a module $\mathcal{L}'$ on the base change satisfying `IsCanonicalPolData` for $L'$, the base-changed $\Lambda$-action and $\mathrm{star}$. (huniq) For every $S$-algebra $R$, every compatible relative group law $L'$ on $E.A\times_{\operatorname{Spec} S}\operatorname{Spec} R$ and any two modules satisfying `IsCanonicalPolData` for these data, the two modules are `LocIsoOnBase`, i.e. every point of $\operatorname{Spec} R$ has an open neighbourhood $U$ over whose preimage the two modules become isomorphic. The conclusion is that there exists a module $\mathcal{L}$ on $E.A$ with `E.IsCanonicalPol star 𝓛`: $\mathcal{L}$ is invertible, symmetric and has two-torsion kernel for $E.L$, satisfies the same fppf-local clause (a faithfully flat $S\to S'$ over which, for every compatible group law, the pullback of $\mathcal{L}$ is locally on the base a product $\mathcal{L}_0\otimes[-1]^*\mathcal{L}_0$ with $\mathcal{L}_0$ invertible of trivial kernel), has strictly positive $H^0$ rank on every geometric fibre, and is Rosati-compatible with $E.\mathrm{act}$ and $\mathrm{star}$.
--
--   This is the descent step in the construction of the canonical polarisation on a fake elliptic curve with quaternionic multiplication by a maximal order in the indefinite quaternion algebra ramified exactly at $q$ and $q'$: flat-local existence of the canonical datum together with its uniqueness up to local isomorphism after arbitrary base change yields the datum over the given base $S$. It feeds the construction of the polarisation under the hypothesis that $2$ is invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isCanonicalPol_of_faithfullyFlat_of_forall_locIsoOnBase.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isCanonicalPol_of_faithfullyFlat_of_forall_locIsoOnBase
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S)
    (hH0 : ∀ (T : Type) [CommRing T] [Algebra S T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd E.f (Scheme.TwoAffineOpenCover.specMap S T)) ⊤
      Function.Bijective (algebraMap T Γ(pullback E.f (Scheme.TwoAffineOpenCover.specMap S T), ⊤)))
    (hloc : ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S'),
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
            star 𝓛')
    (huniq : ∀ (R : Type) [CommRing R] [Algebra S R]
      (L' : RelativeGroupLaw R (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))),
      (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
      ∀ (𝓛 𝓛' : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))).Modules),
        CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L'
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓛 →
        CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L'
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓛' →
        LocIsoOnBase (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) 𝓛 𝓛') :
    ∃ 𝓛 : E.A.Modules, E.IsCanonicalPol star 𝓛 := by sorry
