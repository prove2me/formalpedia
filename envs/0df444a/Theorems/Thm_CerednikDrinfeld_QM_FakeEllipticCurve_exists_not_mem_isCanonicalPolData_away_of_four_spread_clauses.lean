-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_not_mem_isCanonicalPolData_away_of_four_spread_clauses
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_not_mem_isCanonicalPolData_away_of_four_spread_clauses
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/44267b48-945f-5b95-aef2-253091b05e31
-- title:
--   Canonical polarisation datum spreads from S_𝔭 to S_g
-- statement:
--   **Setting.** Two primes $q$ and $q'$ with $q'\neq q$ are fixed, together with rationals $a,b$ such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds for the quaternion algebra $\mathbb H[\mathbb Q,a,b]$: namely $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb Q$ the condition that every nonzero element of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a unit holds exactly when $q\in v$ or $q'\in v$. Further data: a $\mathbb Z$-submodule $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ which is a maximal order (an order — containing $1$, closed under multiplication, spanning the algebra over $\mathbb Q$, finitely generated — and maximal among orders containing it); an element $\mu\in\Lambda$ with $\mu^2=-(qq')\cdot 1$; a function $\mathrm{star}:\Lambda\to\Lambda$ satisfying $\mu\cdot\mathrm{star}(x)=\bar x\,\mu$ for all $x\in\Lambda$, where $\bar x$ is the quaternionic conjugate; a natural number $N$; a noetherian commutative ring $S$ in which $2$ is a unit; and $E$ a term of the structure `FakeEllipticCurve Λ N S`, whose components used below are its total space with structure morphism $E.f$ to $\operatorname{Spec} S$, its commutative relative group law $E.L$, an `AbelianSchemePropertyBundle` for $E.f$ (smooth, proper, connected fibres, a relative group law exists), fibres of topological Krull dimension $2$, and an action $E.\mathrm{act}:\Lambda\to\operatorname{End}(A)$ over the base, additive and multiplicative in $\Lambda$, compatible with the group law and subject to a trace condition on tangent spaces at geometric points, along with the remaining data of that structure.
--
--   **Compatibility of base-changed group laws.** For a commutative $S$-algebra $T$ write $A_T$ for the pullback of $E.f$ along $\operatorname{Spec}$ of the structure map $S\to T$, with projections $p_1$ (to $A$) and $p_2$ (to $\operatorname{Spec} T$). A relative group law $L'$ on $p_2$ is called *compatible* with a given law $L$ on $f$ when, for every scheme $T'$, every morphism $t':T'\to\operatorname{Spec} T$ and all points $P,Q$ of $A_T$ over $t'$, the underlying morphism of $L'.\mathrm{mul}\,t'\,P\,Q$ followed by $p_1$ equals the underlying morphism of the $L$-product of $P\circ p_1$ and $Q\circ p_1$ over $t'$ followed by $\operatorname{Spec}$ of the structure map. This is the shape of every compatibility clause appearing below.
--
--   **The four spreading hypotheses.** Each of `hKSPREAD`, `hLRC`, `hPOS`, `hROS` is itself a universally quantified statement, over an arbitrary noetherian commutative base ring (shadowing the ambient $S$), an arbitrary scheme $A$ with structure morphism $f$ to its spectrum, a relative group law $L$ on $f$, an `AbelianSchemePropertyBundle` for $f$, an invertible module $\mathcal L$ on $A$ (every point has an open neighbourhood on which the restriction of $\mathcal L$ is isomorphic to the unit sheaf of modules), and a prime $\mathfrak p$ of the base; all four conclude with the existence of some $g\notin\mathfrak p$.
--
--   `hKSPREAD` (two-torsion kernel): if for every group law $L'$ over `Localization.AtPrime 𝔭.asIdeal` compatible with $L$ the predicate `KernelIsTwoTorsion` holds for $p_1^{*}\mathcal L$ — that is, for every commutative ring $R$, every $t:\operatorname{Spec}R\to$ the base and every point $x$ over $t$, the pullback of the Mumford bundle $m^{*}\mathcal M\otimes(p_1^{*}\mathcal M^{\vee}\otimes p_2^{*}\mathcal M^{\vee})$ along the slice at $x$ is locally isomorphic, over the base, to the unit object if and only if $x\cdot x$ equals the identity section — then the same holds over `Localization.Away g` for some $g\notin\mathfrak p$.
--
--   `hLRC` (local root cover): given in addition a ring $W$ which is an algebra over the base and over the localisation at $\mathfrak p$, forming a scalar tower and faithfully flat over that localisation, and given that over $W$ every compatible group law $L'$ admits an invertible $\mathcal L_0$ with `KernelTrivial`, `IsSymmetric` and with $p_1^{*}\mathcal L$ locally isomorphic on the base to $\mathcal L_0\otimes(\mathrm{negMor})^{*}\mathcal L_0$, then there are $g\notin\mathfrak p$ and a commutative ring $C$, an algebra over the base and over `Localization.Away g` in a scalar tower, which is finite, faithfully flat and of finite presentation over `Localization.Away g`, such that the same root statement holds over $C$.
--
--   `hPOS` (positivity of $h^0$): given in addition that `KernelIsTwoTorsion f L 𝓛` holds, and that for every algebraically closed field $k$ and every ring homomorphism $sk$ from the base to $k$ which is nonzero on every element outside $\mathfrak p$ the rank `Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk` is positive, then there is $g\notin\mathfrak p$ such that this rank is positive for every algebraically closed $k$ and every $sk$ with $sk(g)\neq 0$.
--
--   `hROS` (Rosati compatibility): given in addition an index type $I$, a family $\mathrm{act}:I\to\operatorname{End}(A)$ of endomorphisms over $f$ and a map $\mathrm{star}:I\to I$, and given that over the localisation at $\mathfrak p$, for every compatible group law $L'$ and every lift $\mathrm{act}'$ of the family to endomorphisms over the localised base intertwining with $\mathrm{act}$ through $p_1$, the predicate `RosatiCompatible` holds for $p_1^{*}\mathcal L$ (for each $b\in I$ the pullbacks of the Mumford bundle along $(p_1,\;p_2\!\cdot\!\mathrm{act}'(b))$ and along $(p_1\!\cdot\!\mathrm{act}'(\mathrm{star}\,b),\;p_2)$ are locally isomorphic over the base), then the same holds over `Localization.Away g` for some $g\notin\mathfrak p$.
--
--   **Input at $\mathfrak p$.** A prime $\mathfrak p$ of $S$ is fixed, subject to two hypotheses. The hypothesis `h𝔭` asserts the existence of a commutative ring $W$, an $S$-algebra and an algebra over $S_{\mathfrak p}=$ `Localization.AtPrime 𝔭.asIdeal` in a scalar tower, faithfully flat over $S_{\mathfrak p}$, such that for every group law $L'$ on $A_W$ compatible with $E.L$ there exist a module $\mathcal L'$ on $A_W$ with `IsCanonicalPolData` for $L'$, the base change of the $\Lambda$-action (sending $x\in\Lambda$ to the morphism with components $p_1$ followed by $E.\mathrm{act}(x)$, and $p_2$), the map $\mathrm{star}$ and $\mathcal L'$, and moreover an invertible $\mathcal L_0$ on $A_W$ with `KernelTrivial`, `IsSymmetric`, and $\mathcal L'$ locally isomorphic on the base to $\mathcal L_0\otimes(\mathrm{negMor})^{*}\mathcal L_0$. The hypothesis `hdat𝔭` asserts that for every group law $L'$ on $A_{S_{\mathfrak p}}$ compatible with $E.L$ there is a module $\mathcal L'$ on $A_{S_{\mathfrak p}}$ satisfying `IsCanonicalPolData` for $L'$, the base-changed $\Lambda$-action, $\mathrm{star}$ and $\mathcal L'$.
--
--   **Conclusion.** There exists $g\in S$ with $g\notin\mathfrak p$ such that, writing $S_g=$ `Localization.Away g` and $A_{S_g}$ for the base change of $E.f$ to $\operatorname{Spec}S_g$, for every relative group law $L'$ on $A_{S_g}$ over $\operatorname{Spec}S_g$ compatible with $E.L$ in the sense above there exists a module $\mathcal L'$ on $A_{S_g}$ such that `IsCanonicalPolData` holds for $p_2$, $L'$, the base-changed $\Lambda$-action $x\mapsto(p_1\cdot E.\mathrm{act}(x),\,p_2)$ together with its commutation with $p_2$, the map $\mathrm{star}$ and $\mathcal L'$; explicitly, all of the following hold.
--
--   (1) $\mathcal L'$ is invertible: every point of $A_{S_g}$ has an open neighbourhood on which the restriction of $\mathcal L'$ is isomorphic to the unit sheaf of modules.
--
--   (2) $\mathcal L'$ is symmetric: the pullback of $\mathcal L'$ along the inversion morphism $\mathrm{negMor}$ of $L'$ and $\mathcal L'$ are locally isomorphic over the base, i.e. every point of $\operatorname{Spec}S_g$ has an open neighbourhood $U$ such that the two restrictions to the preimage of $U$ are isomorphic.
--
--   (3) The kernel of $\mathcal L'$ is two-torsion: for every commutative ring $R$, every $t:\operatorname{Spec}R\to\operatorname{Spec}S_g$ and every point $x$ of $A_{S_g}$ over $t$, the pullback along the slice at $x$ of the Mumford bundle of $\mathcal L'$ is locally isomorphic over the base to the unit object if and only if $L'.\mathrm{mul}\,t\,x\,x=L'.\mathrm{one}\,t$.
--
--   (4) A square root exists after a faithfully flat extension: there are a commutative ring $S''$ and an $S_g$-algebra structure on it with $S''$ faithfully flat over $S_g$, such that for every group law $L''$ on the base change of $p_2$ to $S''$ compatible with $L'$ there is an invertible module $\mathcal L_0$ on that base change with `KernelTrivial`, and with the pullback of $\mathcal L'$ along the first projection locally isomorphic over the base to $\mathcal L_0\otimes(\mathrm{negMor})^{*}\mathcal L_0$.
--
--   (5) Positivity on geometric fibres: for every algebraically closed field $k$ and every ring homomorphism $sk:S_g\to k$, the rank `Scheme.Modules.geomFibreH0Finrank` of the global sections of the pullback of $\mathcal L'$ to the geometric fibre is positive.
--
--   (6) Rosati compatibility: for every $x\in\Lambda$, the pullbacks of the Mumford bundle of $\mathcal L'$ along the two morphisms $(p_1,\;p_2\!\cdot\!\mathrm{act}'(x))$ and $(p_1\!\cdot\!\mathrm{act}'(\mathrm{star}\,x),\;p_2)$, where $\mathrm{act}'$ is the base-changed $\Lambda$-action, are locally isomorphic over the base.
--
--   This is the packaging step in the construction of canonical polarisation data on fake elliptic curves attached to an indefinite quaternion algebra ramified exactly at $q$ and $q'$: a canonical datum known over the local ring $S_{\mathfrak p}$, together with a symmetric square root after a faithfully flat cover, is spread to a Zariski-open neighbourhood $\operatorname{Spec}S_g$ of $\mathfrak p$, the four separate spreading principles for the two-torsion kernel, the root cover, fibrewise positivity and Rosati compatibility being taken as hypotheses. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_not_mem_isCanonicalPolData_away_of_isCanonicalPolData_atPrime_of_symmetricSqrt`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_not_mem_isCanonicalPolData_away_of_isCanonicalPolData_atPrime_of_symmetricSqrt), and is proved from `exists_not_mem_stage_kernelIsTwoTorsion_isSymmetric_rosatiCompatible_of_isCanonicalPolData_atPrime` and `exists_not_mem_isCanonicalPolData_away_of_stage_datum`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_not_mem_isCanonicalPolData_away_of_four_spread_clauses.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_not_mem_isCanonicalPolData_away_of_four_spread_clauses
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
    (hLRC : (∀ {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (𝔭 : PrimeSpectrum S)
    (W : Type) [CommRing W] [Algebra S W] [Algebra (Localization.AtPrime 𝔭.asIdeal) W]
    [IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) W] (hW : Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) W)
    (hroot : (∀ (L' : RelativeGroupLaw W (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of W))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S W)))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S W)))).Modules,
            Scheme.Modules.IsInvertible 𝓛₀ ∧
            KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L' 𝓛₀ ∧
            IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L' 𝓛₀ ∧
            LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
              ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))))).obj 𝓛)
              (𝓛₀ ⊗ (Scheme.Modules.pullback
                (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L')).obj 𝓛₀))),
      ∃ (g : S) (_ : g ∉ 𝔭.asIdeal) (C : Type) (_ : CommRing C) (_ : Algebra S C) (_ : Algebra (Localization.Away g) C)
      (_ : IsScalarTower S (Localization.Away g) C),
      Module.Finite (Localization.Away g) C ∧ Module.FaithfullyFlat (Localization.Away g) C ∧
      Algebra.FinitePresentation (Localization.Away g) C ∧
      (∀ (L' : RelativeGroupLaw C (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of C))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S C)))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C)))).Modules,
            Scheme.Modules.IsInvertible 𝓛₀ ∧
            KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C)))) L' 𝓛₀ ∧
            IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C)))) L' 𝓛₀ ∧
            LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))))
              ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))))).obj 𝓛)
              (𝓛₀ ⊗ (Scheme.Modules.pullback
                (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C)))) L')).obj 𝓛₀))))
    (hPOS : (∀ {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hK : KernelIsTwoTorsion f L 𝓛)
    (𝔭 : PrimeSpectrum S)
    (hpos : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
      (∀ s : S, s ∉ 𝔭.asIdeal → sk s ≠ 0) → 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk),
      ∃ g : S, g ∉ 𝔭.asIdeal ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), sk g ≠ 0 → 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk))
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
    (h𝔭 : ∃ (W : Type) (_ : CommRing W) (_ : Algebra S W) (_ : Algebra (Localization.AtPrime 𝔭.asIdeal) W)
        (_ : IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) W),
        Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) W ∧
      ∀ (L' : RelativeGroupLaw W (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
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
            star 𝓛' ∧
          ∃ 𝓛₀ : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))).Modules,
            Scheme.Modules.IsInvertible 𝓛₀ ∧
            KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L' 𝓛₀ ∧
            IsSymmetric (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L' 𝓛₀ ∧
            LocIsoOnBase (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
              𝓛'
              (𝓛₀ ⊗ (Scheme.Modules.pullback
                (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L')).obj 𝓛₀))
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
            star 𝓛') :
    ∃ g : S, g ∉ 𝔭.asIdeal ∧
      ∀ (L' : RelativeGroupLaw (Localization.Away g) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of (Localization.Away g)))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛' : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))).Modules,
          CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))) L'
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓛' := by sorry
