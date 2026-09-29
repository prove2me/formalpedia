-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_faithfullyFlat_isCanonicalPolData_pullback_of_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_faithfullyFlat_isCanonicalPolData_pullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/3f107b93-5a95-5c7e-9ede-f0527847a908
-- title:
--   Local existence of canonical polarisation data descends along base change
-- statement:
--   Fix primes $q \ne q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for each finite place $v$ of $\mathbb{Q}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is a maximal order (an order contained in no strictly larger order), $\mu \in \Lambda$ with $\mu^2 = -(qq')\cdot 1$, and $star : \Lambda \to \Lambda$ a map with $\mu\cdot star(x) = \bar{x}\cdot\mu$ for all $x$. Let $N \in \mathbb{N}$, let $\varphi : S_1 \to S$ be a homomorphism of commutative rings, and let $E_1$, $E$ be fake elliptic curves for $(\Lambda,N)$ over $S_1$ and over $S$ respectively, with $E$ a base change of $E_1$ along $\varphi$ in the sense of `FakeEllipticCurve.IsPullback`: there is $g : E.A \to E_1.A$ making the square with the structure maps and $\operatorname{Spec}\varphi$ cartesian, carrying the relative group law of $E$ to that of $E_1$, intertwining the $\Lambda$-actions, and sending points factoring through the level structure of $E$ to points factoring through that of $E_1$. Assume of $E_1$ the following local existence statement: there is a faithfully flat $S_1$-algebra $S_1'$ such that for every relative group law $L'$ on the projection $E_1.A \times_{\operatorname{Spec} S_1} \operatorname{Spec} S_1' \to \operatorname{Spec} S_1'$ whose multiplication is compatible, via the first projection, with the group law of $E_1$, there exists a module $\mathcal{L}'$ on the pullback scheme satisfying `IsCanonicalPolData` for $L'$, for the $\Lambda$-action obtained from $E_1.act$ by pullback, and for $star$ — that is: $\mathcal{L}'$ is invertible, symmetric (locally on the base isomorphic to its pullback along the inversion morphism), its kernel is two-torsion, after a further faithfully flat base change it becomes trivial-kernel and satisfies the Mumford-type local isomorphism condition, its geometric fibre $H^0$ has positive finrank at every algebraically closed point of the base, and it is Rosati-compatible with the action and $star$. The conclusion is the same statement for $E$ over $S$: there is a faithfully flat $S$-algebra $S'$ such that every compatible relative group law on $E.A \times_{\operatorname{Spec} S} \operatorname{Spec} S' \to \operatorname{Spec} S'$ admits such a canonical polarisation datum, for the pulled-back $\Lambda$-action and the same $star$.
--
--   This is the base-change step in the construction of the canonical polarisation on fake elliptic curves in the Čerednik–Drinfel'd setting: the fppf-local existence of a canonical polarisation datum, with its Rosati compatibility for the maximal order $\Lambda$ and the involution determined by $\mu$, is transported from a fake elliptic curve to any of its base changes. It is cited in the reduction of local existence to the case where $2$ is invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_faithfullyFlat_isCanonicalPolData_pullback_of_isPullback.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_faithfullyFlat_isCanonicalPolData_pullback_of_isPullback
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S₁ S : Type) [CommRing S₁] [CommRing S] (φ : S₁ →+* S)
    (E₁ : FakeEllipticCurve Λ N S₁) (E : FakeEllipticCurve Λ N S) (hE : FakeEllipticCurve.IsPullback φ E₁ E)
    (h₁ : ∃ (S₁₁' : Type) (_ : CommRing S₁₁') (_ : Algebra S₁ S₁₁'),
        Module.FaithfullyFlat S₁ S₁₁' ∧
        ∀ (L' : RelativeGroupLaw S₁₁' (pullback.snd E₁.f (Spec.map (CommRingCat.ofHom (algebraMap S₁ S₁₁'))))),
          (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of S₁₁'))
              (P Q : SchemeHomOver t' (pullback.snd E₁.f (Spec.map (CommRingCat.ofHom (algebraMap S₁ S₁₁'))))),
              (L'.mul t' P Q).1 ≫ pullback.fst E₁.f (Spec.map (CommRingCat.ofHom (algebraMap S₁ S₁₁'))) =
                (E₁.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S₁ S₁₁'))))
                  ⟨P.1 ≫ pullback.fst E₁.f (Spec.map (CommRingCat.ofHom (algebraMap S₁ S₁₁'))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst E₁.f (Spec.map (CommRingCat.ofHom (algebraMap S₁ S₁₁'))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∃ 𝓛' : (pullback E₁.f (Spec.map (CommRingCat.ofHom (algebraMap S₁ S₁₁')))).Modules,
            CerednikDrinfeld.QM.IsCanonicalPolData
              (pullback.snd E₁.f (Spec.map (CommRingCat.ofHom (algebraMap S₁ S₁₁')))) L'
              (fun x : ↥Λ => pullback.lift (pullback.fst E₁.f (Spec.map (CommRingCat.ofHom (algebraMap S₁ S₁₁'))) ≫ E₁.act x) (pullback.snd E₁.f (Spec.map (CommRingCat.ofHom (algebraMap S₁ S₁₁'))))
                (by rw [Category.assoc, E₁.act_over]; exact pullback.condition))
              (fun x => pullback.lift_snd _ _ _)
              star 𝓛') :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S'),
      Module.FaithfullyFlat S S' ∧
      ∀ (L' : RelativeGroupLaw S' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of S'))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))),
                  by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))),
                  by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛' : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules,
          CerednikDrinfeld.QM.IsCanonicalPolData
            (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L'
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓛' := by sorry
