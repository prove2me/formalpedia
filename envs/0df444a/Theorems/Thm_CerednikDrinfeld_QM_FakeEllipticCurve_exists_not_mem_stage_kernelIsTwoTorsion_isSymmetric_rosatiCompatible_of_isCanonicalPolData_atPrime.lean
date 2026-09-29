-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_not_mem_stage_kernelIsTwoTorsion_isSymmetric_rosatiCompatible_of_isCanonicalPolData_atPrime
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_not_mem_stage_kernelIsTwoTorsion_isSymmetric_rosatiCompatible_of_isCanonicalPolData_atPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/b55fa0dd-e6cb-5ee4-a3c7-e75df85ec591
-- title:
--   Spreading a canonical polarisation datum from S_𝔭 to S_{g_0}
-- statement:
--   Throughout, $q$ and $q'$ are primes with $q' \neq q$, and $a,b \in \mathbb{Q}$ are such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds for the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$: by definition, $0 < a$ or $0 < b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements invertible precisely when $q \in v$ or $q' \in v$. Further data: a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order (an order, and the only order containing it); an element $\mu \in \Lambda$ with $\mu^2 = -(qq') \cdot 1$; and a map $\mathrm{star} : \Lambda \to \Lambda$ satisfying $\mu \cdot \mathrm{star}(x) = \bar{x} \cdot \mu$ for all $x \in \Lambda$, where $\bar{\ }$ is quaternionic conjugation. Finally, $N$ is a natural number, $S$ is a noetherian commutative ring in which $2$ is a unit, and $E$ is a term of `FakeEllipticCurve Λ N S`: a scheme $A = E.A$ with a structure morphism $E.f : A \to \operatorname{Spec} S$, a commutative relative group law $E.L$ on $E.f$, an `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, a group law exists), all fibres of topological Krull dimension $2$, an action $E.\mathrm{act} : \Lambda \to \operatorname{End}(A)$ by morphisms over $\operatorname{Spec} S$ which is additive and multiplicative in the appropriate sense and satisfies the trace condition on tangent spaces, together with the remaining fields of the structure (level-$N$ and curve data).
--
--   For a commutative $S$-algebra $S'$ write $A_{S'} = A \times_{\operatorname{Spec} S} \operatorname{Spec} S'$ for the pullback of $E.f$ along $\operatorname{Spec}$ of the structure map, with projections `pullback.fst` and `pullback.snd`. A relative group law $L'$ on $A_{S'} \to \operatorname{Spec} S'$ is called *compatible* below when for all schemes $T$, all $t' : T \to \operatorname{Spec} S'$ and all $T$-points $P,Q$ of $A_{S'}$ over $t'$, the first projection of $L'.\mathrm{mul}\,t'\,P\,Q$ agrees with the $E.L$-product of the images of $P$ and $Q$ under the first projection; this is exactly the clause written out in each of the quantifiers below. For $x \in \Lambda$ the base change of $E.\mathrm{act}\,x$ to $A_{S'}$ is the morphism $\mathrm{lift}(\mathrm{fst} \circ (E.\mathrm{act}\,x), \mathrm{snd})$, a morphism over $\operatorname{Spec} S'$; together with $\mathrm{star}$ it is the action datum used in the Rosati clauses.
--
--   Two hypotheses of spreading type are assumed, each stated for arbitrary noetherian base, arbitrary abelian-scheme datum and arbitrary invertible module, and each concluding over a basic open:
--
--   `hKSPREAD` (kernel spreading): for every noetherian commutative ring $S$, every $f : A \to \operatorname{Spec} S$ with a relative group law $L$ and an `AbelianSchemePropertyBundle`, every invertible module $\mathcal{L}$ on $A$, and every prime $\mathfrak{p}$ of $S$: if for every compatible relative group law $L'$ on $A_{S_{\mathfrak p}}$ the property `KernelIsTwoTorsion` holds for $L'$ and the pullback of $\mathcal{L}$ along the first projection, then there exists $g \notin \mathfrak{p}$ for which the same holds over the localisation away from $g$. Here `KernelIsTwoTorsion` asserts, for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec}$ of the base and every point $x$ of the abelian scheme over $t$, that the Mumford bundle of the datum, pulled back along the slice at $x$, is isomorphic to the unit object locally on the base if and only if $x + x$ equals the identity section.
--
--   `hROS` (Rosati spreading): in the same generality, with in addition a type $I$, a family $\mathrm{act} : I \to \operatorname{End}(A)$ of morphisms over the base and a map $\mathrm{star} : I \to I$: if for every prime $\mathfrak{p}$, every compatible relative group law $L'$ on $A_{S_{\mathfrak p}}$ and every family $\mathrm{act}'$ of endomorphisms of $A_{S_{\mathfrak p}}$ over $\operatorname{Spec} S_{\mathfrak p}$ lifting $\mathrm{act}$ (that is, commuting with the first projection) the property `RosatiCompatible` holds for $L'$, the pullback of $\mathcal{L}$, $\mathrm{act}'$ and $\mathrm{star}$, then there exists $g \notin \mathfrak{p}$ for which the same holds over the localisation away from $g$. Here `RosatiCompatible` asserts that for each $b \in I$ the two pullbacks of the Mumford bundle, along $(\mathrm{fst}, \mathrm{snd} \circ \mathrm{act}\,b)$ and along $(\mathrm{fst} \circ \mathrm{act}(\mathrm{star}\,b), \mathrm{snd})$, are isomorphic locally on the base.
--
--   `hdat𝔭` (datum at the prime): for the given prime $\mathfrak{p}$ of $S$ and every compatible relative group law $L'$ on $A_{S_{\mathfrak p}} \to \operatorname{Spec} S_{\mathfrak p}$ there exists a module $\mathcal{L}'$ on $A_{S_{\mathfrak p}}$ with `IsCanonicalPolData` for $L'$, the base-changed $\Lambda$-action and $\mathrm{star}$; by definition this conjoins: invertibility of $\mathcal{L}'$; symmetry, i.e. the pullback of $\mathcal{L}'$ along the inversion morphism is isomorphic to $\mathcal{L}'$ locally on the base; `KernelIsTwoTorsion`; the existence of a faithfully flat algebra $S''$ over the base such that for every compatible group law on the further base change there is an invertible module $\mathcal{L}_0$ with trivial kernel and with the pullback of $\mathcal{L}'$ isomorphic, locally on the base, to $\mathcal{L}_0 \otimes [-1]^*\mathcal{L}_0$; positivity of the geometric fibre $H^0$ finrank over every algebraically closed field with a ring map from the base; and `RosatiCompatible`.
--
--   The conclusion asserts the existence of an element $g_0 \in S$ with $g_0 \notin \mathfrak{p}$, a ring homomorphism $\psi : S_{g_0} \to S_{\mathfrak p}$ from the localisation away from $g_0$ to the localisation at $\mathfrak{p}$ with $\psi$ composed with the structure map of $S_{g_0}$ equal to the structure map of $S_{\mathfrak p}$, and a module $\mathcal{M}$ on $A_{S_{g_0}}$, such that the following three conjuncts hold.
--
--   First, $\mathcal{M}$ is invertible: every point of $A_{S_{g_0}}$ has an open neighbourhood on which $\mathcal{M}$ restricts to a trivial module.
--
--   Second, for every relative group law $L'$ on $A_{S_{g_0}} \to \operatorname{Spec} S_{g_0}$ compatible with $E.L$ in the above sense, the triple of properties holds for $L'$ and $\mathcal{M}$: `KernelIsTwoTorsion`, `IsSymmetric` (the pullback of $\mathcal{M}$ along the inversion morphism of $L'$ is isomorphic to $\mathcal{M}$ locally on the base), and `RosatiCompatible` with respect to the base-changed $\Lambda$-action and $\mathrm{star}$.
--
--   Third, for every compatible relative group law $L'$ on $A_{S_{\mathfrak p}} \to \operatorname{Spec} S_{\mathfrak p}$, the pullback of $\mathcal{M}$ along the comparison morphism $A_{S_{\mathfrak p}} \to A_{S_{g_0}}$ determined by $\psi$, namely $\mathrm{lift}(\mathrm{fst}, \mathrm{snd} \circ \operatorname{Spec}\psi)$, satisfies `IsCanonicalPolData` for $L'$, the base-changed $\Lambda$-action and $\mathrm{star}$, in the full sense recalled above.
--
--   This is the spreading-out step in the construction of a canonical polarisation on a fake elliptic curve: a polarisation datum available over the local ring at a prime $\mathfrak p$, with kernel the $2$-torsion, symmetric and compatible with the Rosati involution of the maximal order $\Lambda$, is realised by an invertible module over a basic open neighbourhood of $\mathfrak p$, agreeing with the given datum after pullback to $\operatorname{Spec} S_{\mathfrak p}$. It feeds [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_not_mem_isCanonicalPolData_away_of_four_spread_clauses`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_not_mem_isCanonicalPolData_away_of_four_spread_clauses), which assembles the clauses into a canonical polarisation datum over the open.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_not_mem_stage_kernelIsTwoTorsion_isSymmetric_rosatiCompatible_of_isCanonicalPolData_atPrime.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_not_mem_stage_kernelIsTwoTorsion_isSymmetric_rosatiCompatible_of_isCanonicalPolData_atPrime
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] [IsNoetherianRing S] (h2 : IsUnit (2 : S)) (E : FakeEllipticCurve Λ N S)
(hKSPREAD : (∀ {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (𝔭 : PrimeSpectrum S)
    (h𝔭 : (∀ (L' : RelativeGroupLaw (Localization.AtPrime 𝔭.asIdeal) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          KernelIsTwoTorsion (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))) L'
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))).obj 𝓛))),
      ∃ g : S, g ∉ 𝔭.asIdeal ∧
      (∀ (L' : RelativeGroupLaw (Localization.Away g) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (Localization.Away g)))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          KernelIsTwoTorsion (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))) L'
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))).obj 𝓛))))
        (hROS : (∀ {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (star : I → I)
    (𝔭 : PrimeSpectrum S)
    (h𝔭 : (∀ (L' : RelativeGroupLaw (Localization.AtPrime 𝔭.asIdeal) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∀ (act' : I → (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ⟶
              pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))))
            (act'_over : ∀ x : I, act' x ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
              pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))),
            (∀ x : I, act' x ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
              pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ≫ act x) →
          RosatiCompatible (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))) L'
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))).obj 𝓛)
            act' act'_over star)),
      ∃ g : S, g ∉ 𝔭.asIdeal ∧
      (∀ (L' : RelativeGroupLaw (Localization.Away g) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (Localization.Away g)))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∀ (act' : I → (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))) ⟶
              pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))))
            (act'_over : ∀ x : I, act' x ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))) =
              pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))),
            (∀ x : I, act' x ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))) =
              pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))) ≫ act x) →
          RosatiCompatible (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))) L'
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))).obj 𝓛)
            act' act'_over star)))
    (𝔭 : PrimeSpectrum S)
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
            star 𝓛')
    :
    ∃ (g₀ : S) (hg₀ : g₀ ∉ 𝔭.asIdeal) (ψ : Localization.Away g₀ →+* Localization.AtPrime 𝔭.asIdeal)
    (hψ : ψ.comp (algebraMap S (Localization.Away g₀)) = algebraMap S (Localization.AtPrime 𝔭.asIdeal))
    (𝓜 : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))))).Modules),
      Scheme.Modules.IsInvertible 𝓜 ∧
      (∀ (L' : RelativeGroupLaw (Localization.Away g₀) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of (Localization.Away g₀)))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        KernelIsTwoTorsion (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))))) L' 𝓜 ∧
        IsSymmetric (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))))) L' 𝓜 ∧
        RosatiCompatible (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))))) L' 𝓜
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _) star) ∧
      (∀ (L' : RelativeGroupLaw (Localization.AtPrime 𝔭.asIdeal) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))) L'
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star
          ((Scheme.Modules.pullback (pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
              (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ≫ Spec.map (CommRingCat.ofHom ψ))
              (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]) :
              pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ⟶
                pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))).obj 𝓜)) := by sorry
