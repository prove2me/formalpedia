-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPolData_pullback_of_isUnit_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPolData_pullback_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/88e09775-adc6-54ee-b5bd-ee9ddda0f67a
-- title:
--   Uniqueness of the canonical polarisation datum after base change
-- statement:
--   Fix primes $q\neq q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, at each finite place $v$ of $\mathbb{Q}$, is a division algebra precisely when $v$ lies above $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a maximal order (an order containing no strictly larger order), let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ be a map with $\mu\cdot\mathrm{star}(x)=\bar{x}\mu$ for all $x\in\Lambda$. Let $N$ be a natural number, $S$ a commutative ring in which $2$ is a unit, and $E$ a fake elliptic curve over $S$ for $\Lambda$ with level $N$, with structure morphism `E.f`, commutative relative group law `E.L` and $\Lambda$-action `E.act`. The conclusion is: for every $S$-algebra $R$, every relative group law $L'$ on the projection $A\times_S\operatorname{Spec}R\to\operatorname{Spec}R$ which is compatible with `E.L` along the first projection (on $T$-points, the first projection of a product computed by $L'$ is the product computed by `E.L`), and any two modules $\mathcal{L},\mathcal{L}'$ on $A\times_S\operatorname{Spec}R$, if each satisfies the project's predicate `IsCanonicalPolData` for $L'$, the action of $\Lambda$ obtained from `E.act` by base change, and $\mathrm{star}$ — i.e. it is invertible, symmetric under the inversion morphism, its Mumford bundle has kernel exactly the $2$-torsion, after some faithfully flat base change its pullback splits locally as $\mathcal{L}_0\otimes[-1]^*\mathcal{L}_0$ with $\mathcal{L}_0$ invertible of trivial kernel, all geometric fibres have positive $H^0$-rank, and it is Rosati-compatible with the action and $\mathrm{star}$ — then $\mathcal{L}$ and $\mathcal{L}'$ are isomorphic locally on the base: every point of $\operatorname{Spec}R$ has an open neighbourhood $U$ whose preimage carries an isomorphism between the restrictions of $\mathcal{L}$ and $\mathcal{L}'$.
--
--   This is the uniqueness, up to isomorphism locally on the base, of the canonical polarisation datum on a fake elliptic curve, in the form needed after an arbitrary affine base change rather than only over the original base $S$; the hypothesis that $2$ be invertible reflects the division by $2$ in the fibrewise argument. It is used in the construction of a canonical polarisation on a fake elliptic curve and in the descent arguments that compare such data over two base changes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPolData_pullback_of_isUnit_two.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPolData_pullback_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (h2 : IsUnit (2 : S)) (E : FakeEllipticCurve Λ N S) :
    ∀ (R : Type) [CommRing R] [Algebra S R]
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
        LocIsoOnBase (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) 𝓛 𝓛' := by sorry
