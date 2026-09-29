-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_faithfullyFlat_isCanonicalPolData_pullback_of_isUnit_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_faithfullyFlat_isCanonicalPolData_pullback_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/96c2b917-a237-58d8-9646-46e19f788675
-- title:
--   Canonical polarisation datum exists faithfully flat locally when 2 is invertible
-- statement:
--   Let $q \neq q'$ be primes and let $a, b \in \mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders for inclusion, let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq') \cdot 1$, and let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu \cdot \mathrm{star}(x) = \bar{x} \mu$ for all $x \in \Lambda$. Let $N \in \mathbb{N}$, let $S$ be a commutative ring in which $2$ is a unit, and let $E$ be a fake elliptic curve over $S$ of level $N$ with $\Lambda$-action, i.e. a structure consisting of a scheme $A$, a morphism $f : A \to \operatorname{Spec} S$, a commutative relative group law $E.L$ on $f$, an abelian-scheme property bundle, fibres of topological Krull dimension $2$, an action $x \mapsto E.\mathrm{act}\,x$ of $\Lambda$ by endomorphisms of $A$ over $S$ which is additive, multiplicative and satisfies the trace condition, together with the level-$N$ data. Then there are a commutative ring $S'$ and an $S$-algebra structure on it making $S'$ a faithfully flat $S$-module such that the following holds for the base change $A' = A \times_{\operatorname{Spec} S} \operatorname{Spec} S'$: for every relative group law $L'$ on the projection $A' \to \operatorname{Spec} S'$ which is compatible with $E.L$ through the other projection $\pi : A' \to A$ (for all schemes $T$, all $t' : T \to \operatorname{Spec} S'$ and all $T$-points $P, Q$ of $A'$ over $t'$, the morphism underlying $L'.\mathrm{mul}\,t'\,P\,Q$ followed by $\pi$ equals the morphism underlying $E.L.\mathrm{mul}$ applied to $P$ followed by $\pi$ and $Q$ followed by $\pi$), there exists a module $\mathcal{L}'$ on $A'$ which is a canonical polarisation datum for $A' \to \operatorname{Spec} S'$, $L'$, the $\Lambda$-action obtained from $E.\mathrm{act}$ by lifting $\pi \circ$ followed by $E.\mathrm{act}\,x$ against the projection, and $\mathrm{star}$: that is, $\mathcal{L}'$ is invertible, symmetric (its pullback along the inversion morphism is locally on the base isomorphic to itself), its Mumford-bundle kernel is exactly the $2$-torsion of $L'$, there is a further faithfully flat base change over which $\mathcal{L}'$ admits, for every compatible group law, a symmetric square root $\mathcal{L}_0$ with trivial kernel, the geometric fibre $H^0$ ranks at all algebraically closed field points are positive, and the Rosati compatibility with the $\Lambda$-action and $\mathrm{star}$ holds.
--
--   This is the local existence half of the canonical (Rosati-compatible) polarisation on a fake elliptic curve over an arbitrary affine base in which $2$ is invertible: the datum is produced only after a faithfully flat extension of the base ring, and is stated in unbundled form for the base-changed group law and quaternionic action. It feeds the global statement [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isCanonicalPol_of_isUnit_two`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isCanonicalPol_of_isUnit_two) used in the Čerednik–Drinfeld part of the construction of Shimura curves attached to the indefinite quaternion algebra ramified exactly at $q$ and $q'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_faithfullyFlat_isCanonicalPolData_pullback_of_isUnit_two.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_faithfullyFlat_isCanonicalPolData_pullback_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (h2 : IsUnit (2 : S)) (E : FakeEllipticCurve Λ N S) :
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
