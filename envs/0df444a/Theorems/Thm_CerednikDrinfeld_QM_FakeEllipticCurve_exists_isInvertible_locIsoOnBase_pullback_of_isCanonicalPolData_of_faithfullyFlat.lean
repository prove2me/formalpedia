-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_locIsoOnBase_pullback_of_isCanonicalPolData_of_faithfullyFlat
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_locIsoOnBase_pullback_of_isCanonicalPolData_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/6b7f38fb-6bc7-57cb-b812-b1b87e83b8a3
-- title:
--   Descent of canonical polarisation data along faithfully flat base change
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $q$ or $q'$ lies in $v$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among the orders containing it, let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq')\cdot 1$, and let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu\,\mathrm{star}(x) = \bar{x}\mu$ for all $x \in \Lambda$. Let $N \in \mathbb{N}$, let $S$ be a commutative ring and let $E$ be a fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ datum, with structure morphism $f : A \to \operatorname{Spec} S$ and relative group law $E.L$. Two hypotheses are imposed on $E$: first, for every $S$-algebra $T$ the structure map $T \to \Gamma(A_T, \top)$ is bijective, where $A_T$ is the fibre product of $f$ with $\operatorname{Spec} T \to \operatorname{Spec} S$; second, uniqueness of canonical data, namely for every $S$-algebra $R$ and every relative group law $L'$ on $A_R$ whose multiplication is compatible with that of $E.L$ under the first projection, any two modules $\mathcal{L},\mathcal{L}'$ on $A_R$ satisfying `IsCanonicalPolData` for $L'$, the transported $\Lambda$-action $x \mapsto \langle \mathrm{fst} \circ E.\mathrm{act}\,x, \mathrm{snd}\rangle$ and $\mathrm{star}$ (the conjunction of: invertibility, symmetry, two-torsion kernel, existence of a faithfully flat base extension over which the pullback becomes, locally on the base, $\mathcal{L}_0 \otimes [-1]^{*}\mathcal{L}_0$ for an invertible $\mathcal{L}_0$ with trivial kernel, positivity of the rank of $H^0$ on every geometric fibre, and Rosati compatibility) are locally isomorphic over the base, i.e. every point of $\operatorname{Spec} R$ has an open neighbourhood $U$ over whose preimage the two modules become isomorphic. Now let $S'$ be an $S$-algebra which is faithfully flat as an $S$-module, let $L'$ be a relative group law on $A_{S'}$ whose multiplication is compatible with $E.L$ under the first projection, and let $\mathcal{L}'$ be a module on $A_{S'}$ satisfying `IsCanonicalPolData` for these data. Then there exists a module $\mathcal{L}$ on $A$ which is invertible (every point of $A$ has an open neighbourhood on which $\mathcal{L}$ restricts to the unit module) and whose pullback along the first projection $A_{S'} \to A$ is isomorphic to $\mathcal{L}'$ locally over $\operatorname{Spec} S'$.
--
--   This is the module-theoretic half of faithfully flat descent for canonical polarisation data on the abelian surface underlying a fake elliptic curve: a datum produced only after a faithfully flat base change is shown to come, up to local isomorphism over the base, from an invertible module on the surface itself. It feeds the construction of a canonical polarisation over the original base in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isCanonicalPol_of_faithfullyFlat_of_forall_locIsoOnBase`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isCanonicalPol_of_faithfullyFlat_of_forall_locIsoOnBase), part of the integral-model theory of Shimura curves used in the Čerednik–Drinfel'd uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_locIsoOnBase_pullback_of_isCanonicalPolData_of_faithfullyFlat.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_locIsoOnBase_pullback_of_isCanonicalPolData_of_faithfullyFlat
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
        LocIsoOnBase (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) 𝓛 𝓛')
    (S' : Type) [CommRing S'] [Algebra S S'] (hff : Module.FaithfullyFlat S S')
    (L' : RelativeGroupLaw S' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))))
    (hL' : (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of S'))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (𝓛' : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules)
    (h𝓛' : CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L'
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓛') :
    ∃ 𝓛 : E.A.Modules, Scheme.Modules.IsInvertible 𝓛 ∧
      LocIsoOnBase (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
        ((Scheme.Modules.pullback (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj 𝓛) 𝓛' := by sorry
