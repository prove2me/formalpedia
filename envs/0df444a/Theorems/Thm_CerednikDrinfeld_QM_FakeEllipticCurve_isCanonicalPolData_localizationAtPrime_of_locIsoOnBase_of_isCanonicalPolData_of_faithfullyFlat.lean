-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isCanonicalPolData_localizationAtPrime_of_locIsoOnBase_of_isCanonicalPolData_of_faithfullyFlat
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isCanonicalPolData_localizationAtPrime_of_locIsoOnBase_of_isCanonicalPolData_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/57721c81-bd13-5592-bc23-7b87e8f06bae
-- title:
--   Descent of a canonical polarisation datum to the local ring
-- statement:
--   Let $q\neq q'$ be primes and $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and its completion at a finite place $v$ of $\mathbb{Q}$ is a division algebra exactly when $v$ contains $q$ or $q'$; let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be an order maximal among orders, $\mu\in\Lambda$ with $\mu^{2}=-(qq')\cdot 1$, and $\mathrm{star}:\Lambda\to\Lambda$ a map with $\mu\,\mathrm{star}(x)=\bar{x}\,\mu$ for all $x\in\Lambda$. Let $N\in\mathbb{N}$, let $S$ be a commutative ring, $E$ a `FakeEllipticCurve` over $S$ for $\Lambda$ and $N$ with abelian scheme $E.A\to\operatorname{Spec}S$, group law $E.L$ and $\Lambda$-action $E.\mathrm{act}$, let $\mathfrak{p}$ be a prime of $S$, and let $W$ be a commutative ring which is an $S$-algebra and an $S_{\mathfrak p}$-algebra compatibly and is faithfully flat over $S_{\mathfrak p}$. Write $A_{S_{\mathfrak p}}\to\operatorname{Spec}S_{\mathfrak p}$ and $A_{W}\to\operatorname{Spec}W$ for the base changes of $E.A$, each carrying the base-changed $\Lambda$-action $x\mapsto E.\mathrm{act}(x)\times\mathrm{id}$. Assume given: relative group laws $L_{\mathfrak p}$ on $A_{S_{\mathfrak p}}/S_{\mathfrak p}$ and $L_{W}$ on $A_{W}/W$ whose multiplications are compatible with that of $E.L$ under the respective first projections to $E.A$; an invertible module $\mathcal{L}_{\mathfrak p}$ on $A_{S_{\mathfrak p}}$; a module $\mathcal{L}_{W}$ on $A_{W}$ which is a canonical polarisation datum for $(A_W/W,L_W)$, the base-changed $\Lambda$-action and $\mathrm{star}$; and a morphism $\rho:A_{W}\to A_{S_{\mathfrak p}}$ commuting with the projections to $E.A$ and covering $\operatorname{Spec}W\to\operatorname{Spec}S_{\mathfrak p}$, such that $\rho^{*}\mathcal{L}_{\mathfrak p}$ and $\mathcal{L}_{W}$ become isomorphic over the preimages of a neighbourhood of each point of $\operatorname{Spec}W$. The conclusion is that $\mathcal{L}_{\mathfrak p}$ is a canonical polarisation datum for $(A_{S_{\mathfrak p}}/S_{\mathfrak p},L_{\mathfrak p})$, the base-changed $\Lambda$-action and $\mathrm{star}$: it is invertible; it is symmetric, i.e. its pullback along the inversion morphism of $L_{\mathfrak p}$ is isomorphic to it locally on $\operatorname{Spec}S_{\mathfrak p}$; the points at which its Mumford bundle becomes trivial locally on the base are exactly the $2$-torsion points of $L_{\mathfrak p}$; there is a faithfully flat $S_{\mathfrak p}$-algebra $S'$ over which, for every compatible group law, $\mathcal{L}_{\mathfrak p}$ admits a square root $\mathcal{L}_0$ that is invertible with trivial kernel, in the sense that the pullback of $\mathcal{L}_{\mathfrak p}$ is locally isomorphic to $\mathcal{L}_0\otimes(-1)^{*}\mathcal{L}_0$; the $h^{0}$ of every geometric fibre is positive; and it is Rosati-compatible with the $\Lambda$-action through $\mathrm{star}$.
--
--   This is the descent step for the canonical polarisation datum on a fake elliptic curve: all six clauses of the datum, being local-on-the-base isomorphism statements between invertible modules together with a kernel condition, a positivity condition on geometric fibres and the existence of a square root after a further faithfully flat extension, pass from a faithfully flat base change $W$ of the local ring $S_{\mathfrak p}$ back down to $S_{\mathfrak p}$. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isCanonicalPolData_localizationAtPrime_of_faithfullyFlat_of_isUnit_two`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isCanonicalPolData_localizationAtPrime_of_faithfullyFlat_of_isUnit_two) to produce such a datum over the local rings of the moduli base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isCanonicalPolData_localizationAtPrime_of_locIsoOnBase_of_isCanonicalPolData_of_faithfullyFlat.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isCanonicalPolData_localizationAtPrime_of_locIsoOnBase_of_isCanonicalPolData_of_faithfullyFlat
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S) (𝔭 : PrimeSpectrum S)
    (W : Type) [CommRing W] [Algebra S W] [Algebra (Localization.AtPrime 𝔭.asIdeal) W]
    [IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) W] (hW : Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) W)
    (L𝔭 : RelativeGroupLaw (Localization.AtPrime 𝔭.asIdeal) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))))
    (hL𝔭 : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)))
          (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
          (L𝔭.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
            (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))
              ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (𝓛𝔭 : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))).Modules) (h𝓛𝔭 : Scheme.Modules.IsInvertible 𝓛𝔭)
    (LW : RelativeGroupLaw W (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))))
    (hLW : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of W))
          (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
          (LW.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))) =
            (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S W)))
              ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (𝓛W : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))).Modules)
    (hdW : CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) LW
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓛W)
    (ρ : pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
    (hρ₁ : ρ ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
    (hρ₂ : ρ ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
      pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))) ≫ Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime 𝔭.asIdeal) W)))
    (hcmp : LocIsoOnBase (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) ((Scheme.Modules.pullback ρ).obj 𝓛𝔭) 𝓛W) :
    CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))) L𝔭
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓛𝔭 := by sorry
