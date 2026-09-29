-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isCanonicalPolData_pi_of_forall
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isCanonicalPolData_pi_of_forall
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/0550a9c3-5292-5499-8861-be5f2ebdc40a
-- title:
--   Canonical polarisation data over a finite product of base algebras
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq')\cdot 1$, and let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu\,\mathrm{star}(x) = \bar{x}\,\mu$ for all $x \in \Lambda$. Let $N$ be a natural number, $S$ a commutative ring and $E$ a fake elliptic curve over $S$ of level $N$ with $\Lambda$-action, so in particular a scheme $A$ with structure morphism $E.f : A \to \operatorname{Spec} S$, a relative group law $E.L$, an abelian-scheme property bundle, two-dimensional fibres, and endomorphisms $E.\mathrm{act}\,x$ over $S$ realising $\Lambda$. Let $C : \mathrm{Fin}\,k \to \mathrm{Type}$ be finitely many commutative $S$-algebras. Assume, for each $i$, that every relative group law $L'$ on the base change $A_{C_i} = A \times_{\operatorname{Spec} S} \operatorname{Spec} C_i$ (taken with its second projection as structure morphism) which is compatible with $E.L$, in the sense that the first projection of a product of two $T$-points is the $E.L$-product of their first projections, admits a module $\mathcal{L}'$ on $A_{C_i}$ satisfying `IsCanonicalPolData` for $L'$, for the $\Lambda$-action obtained by base change of $E.\mathrm{act}$, and for $\mathrm{star}$: that is, $\mathcal{L}'$ is invertible, symmetric (its pullback along the inversion morphism is locally on the base isomorphic to it), the kernel of the associated Mumford bundle consists exactly of the points killed by $2$, there is a faithfully flat algebra over which the pulled-back bundle has a square root with trivial kernel, all geometric fibre $H^0$-ranks are positive, and the Rosati compatibility with $\mathrm{act}$ and $\mathrm{star}$ holds. The conclusion is the same assertion with $C_i$ replaced by the product ring $\prod_i C_i$: every group law on $A_{\prod_i C_i}$ compatible with $E.L$ in the above sense admits a module satisfying `IsCanonicalPolData` for the base-changed $\Lambda$-action and $\mathrm{star}$.
--
--   This is the product step in constructing the canonical polarisation on a fake elliptic curve after base change: since $\operatorname{Spec} \prod_i C_i$ is the disjoint union of the $\operatorname{Spec} C_i$, all six clauses of the canonical-datum predicate are checked piecewise and the bundles glued along the clopen decomposition, the square-root clause taking the product of the witnessing faithfully flat algebras. It feeds the Zariski-to-fppf assembly [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_faithfullyFlat_isCanonicalPolData_of_forall_isMaximal_away`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_faithfullyFlat_isCanonicalPolData_of_forall_isMaximal_away), en route to the Čerednik–Drinfeld uniformisation of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isCanonicalPolData_pi_of_forall.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isCanonicalPolData_pi_of_forall
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S)
    {k : ℕ} (C : Fin k → Type) [∀ i, CommRing (C i)] [∀ i, Algebra S (C i)]
    (hdat : ∀ i, ∀ (L' : RelativeGroupLaw (C i) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of (C i)))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛' : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))).Modules,
          CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))) L'
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓛') :
    ∀ (L' : RelativeGroupLaw (∀ i, C i) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of (∀ i, C i)))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛' : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i))))).Modules,
          CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i))))) L'
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓛' := by sorry
