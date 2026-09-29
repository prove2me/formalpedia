-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_faithfullyFlat_isCanonicalPolData_of_forall_isAdicComplete_charP_symmetricSqrt_of_finiteType
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_faithfullyFlat_isCanonicalPolData_of_forall_isAdicComplete_charP_symmetricSqrt_of_finiteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/873c2108-b952-529b-9dff-231a14f1e31b
-- title:
--   Spreading canonical polarisation data over a finite-type base
-- statement:
--   Fix distinct primes $q' \neq q$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0 < a$ or $0 < b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $v$ lies over $q$ or $q'$. Let $\Lambda \subset \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among orders for inclusion, let $\mu \in \Lambda$ satisfy $\mu^2 = -qq'$, and let $\operatorname{star} : \Lambda \to \Lambda$ satisfy $\mu \cdot \operatorname{star}(x) = \bar{x} \mu$ for all $x \in \Lambda$. Let $N \in \mathbb{N}$, let $S$ be a Noetherian commutative ring of finite type over $\mathbb{Z}$ in which $2$ is a unit, and let $E$ be a fake elliptic curve over $S$ for $\Lambda$ and $N$, with structure morphism $E.f : A \to \operatorname{Spec} S$, relative group law $E.L$ and $\Lambda$-action $E.\mathrm{act}$. Assume the formal-local hypothesis: for every complete local Noetherian $S$-algebra $R$ with algebraically closed residue field of prime characteristic $p$ and with $2 \in R^{\times}$, and every relative group law $L'$ on $A_R = A \times_{\operatorname{Spec} S} \operatorname{Spec} R$ over $R$ whose multiplication is compatible with $E.L$ under the first projection, there is a module $\mathcal{L}_0$ on $A_R$ that is invertible, satisfies `KernelTrivial` for $L'$ (the only point of the base whose associated Mumford bundle is locally trivial on the base is the identity) and `IsSymmetric` (the pullback along the inversion morphism is locally on the base isomorphic to $\mathcal{L}_0$), and such that $\mathcal{L}_0 \otimes [-1]^{*}\mathcal{L}_0$ is a canonical polarisation datum for $L'$, the $\Lambda$-action obtained from $E.\mathrm{act}$ by base change, and $\operatorname{star}$ — that is, it is invertible, symmetric, satisfies `KernelIsTwoTorsion`, admits a square root after a faithfully flat base change in the sense of `IsCanonicalPolData`, has positive geometric fibre $H^0$ rank over every algebraically closed field, and is `RosatiCompatible`. The conclusion: there exist a commutative ring $S'$ and an $S$-algebra structure on it making $S'$ faithfully flat over $S$, such that for every relative group law $L'$ on $A_{S'}$ compatible with $E.L$ in the same sense there is a module $\mathcal{L}'$ on $A_{S'}$ which is a canonical polarisation datum for $L'$, the base-changed $\Lambda$-action and $\operatorname{star}$.
--
--   This is the spreading step for canonical polarisations on fake elliptic curves: it converts the existence of symmetric invertible modules with trivial kernel whose symmetric squares are canonical data over complete local base rings into the existence of a canonical polarisation datum after a single faithfully flat extension of the finite-type base. It is used in the construction of the polarised quaternionic moduli problem underlying the Čerednik–Drinfeld description, and is cited by the pullback form of the same statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_faithfullyFlat_isCanonicalPolData_of_forall_isAdicComplete_charP_symmetricSqrt_of_finiteType.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_faithfullyFlat_isCanonicalPolData_of_forall_isAdicComplete_charP_symmetricSqrt_of_finiteType
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra.FiniteType ℤ S] (h2 : IsUnit (2 : S)) (E : FakeEllipticCurve Λ N S)
    (hformal : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsAlgClosed (IsLocalRing.ResidueField R)] [Algebra S R],
      IsUnit (2 : R) →
      ∀ (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p],
      ∀ (L' : RelativeGroupLaw R (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L' 𝓛₀ ∧
          IsSymmetric (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L' 𝓛₀ ∧
          CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L'
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L')).obj 𝓛₀)) :
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
