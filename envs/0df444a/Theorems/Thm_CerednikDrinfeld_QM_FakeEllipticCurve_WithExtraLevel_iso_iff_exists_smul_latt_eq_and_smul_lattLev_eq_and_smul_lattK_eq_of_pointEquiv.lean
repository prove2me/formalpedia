-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_iff_exists_smul_latt_eq_and_smul_lattLev_eq_and_smul_lattK_eq_of_pointEquiv
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_iff_exists_smul_latt_eq_and_smul_lattLev_eq_and_smul_lattK_eq_of_pointEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/290cd6d2-bb53-5ed8-bbc5-b2184d2f7a09
-- title:
--   Pairs over ℂ are isomorphic iff their lattice triples are homothetic
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $a>0$ or $b>0$ and, for each finite place $v$ of $\mathbb{Q}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ lies above $q$ or $q'$; let $\Lambda \subset \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders containing it, let $\iota : \mathbb{H}[\mathbb{Q},a,b] \to M_2(\mathbb{R})$ be an injective $\mathbb{Q}$-algebra map, and let $N \neq 0$ be a natural number divisible by neither $q$ nor $q'$. Assume given, for every fake elliptic curve $E$ over $\mathbb{C}$ (an abelian scheme datum of relative dimension $2$ with commutative relative group law, $\Lambda$-action and level structure $E.\mathrm{lev}$), a $\mathbb{Z}$-submodule $\mathrm{latt}\,E \subset \mathbb{C}^2$ and a bijection $e_E$ from the $\mathbb{C}$-points of $E$ (sections of $E.f$ over the identity of $\operatorname{Spec}\mathbb{C}$) onto $\mathbb{C}^2/\mathrm{latt}\,E$, subject to: $\mathrm{latt}\,E$ is the $\mathbb{Z}$-span of an $\mathbb{R}$-basis of $\mathbb{C}^2$ indexed by $\mathrm{Fin}\,4$ and is stable under $v \mapsto \iota(x)v$ for $x \in \Lambda$; $e_E$ is additive for the group law; $e_E$ carries the action of $x \in \Lambda$ to multiplication by the complexified matrix $\iota(x)$; every morphism $\varphi : E.A \to E'.A$ over $\operatorname{Spec}\mathbb{C}$ compatible with the group laws and commuting with the $\Lambda$-actions induces, via the $e$'s, multiplication by some $c \in \mathbb{C}$ with $c \cdot \mathrm{latt}\,E \subseteq \mathrm{latt}\,E'$; conversely every such $c$ is realised by a morphism with these properties; and two such morphisms agreeing on $\mathbb{C}$-points are equal. Assume further a second assignment $\mathrm{lattLev}$ such that $v \in \mathrm{lattLev}\,E$ iff $v$ represents $e_E(P)$ for some $\mathbb{C}$-point $P$ factoring through $E.\mathrm{lev}$, with $\mathrm{latt}\,E \le \mathrm{lattLev}\,E$, stability under $\iota(\Lambda)$, $N \cdot \mathrm{lattLev}\,E \subseteq \mathrm{latt}\,E$, and relative index $N^2$. Finally fix a natural number $\ell$ and an assignment $\mathrm{lattK}$ on pairs $u = (E,K)$ with $K$ an extra level structure of level $\ell$, characterised by $v \in \mathrm{lattK}\,u$ iff the point $e_E^{-1}$ of the class of $v$ factors through $u.2.\mathrm{levK}$. The conclusion is that for all such pairs $u, u'$ one has `WithExtraLevel.Iso u u'` — an isomorphism $E.A \cong E'.A$ over $\operatorname{Spec}\mathbb{C}$ compatible with the group laws, commuting with the $\Lambda$-actions, and preserving, for sections over every test base, both factorisation through $\mathrm{lev}$ and factorisation through $\mathrm{levK}$ — if and only if there exists $c \in \mathbb{C}$, $c \neq 0$, with $c \cdot \mathrm{latt}\,E = \mathrm{latt}\,E'$, $c \cdot \mathrm{lattLev}\,E = \mathrm{lattLev}\,E'$ and $c \cdot \mathrm{lattK}\,u = \mathrm{lattK}\,u'$.
--
--   This is the analytic dictionary for fake elliptic curves with level and extra level structure over $\mathbb{C}$: isomorphism classes of such pairs correspond to homothety classes of the associated triples of lattices in $\mathbb{C}^2$, in the style of the classical uniformisation of abelian surfaces with quaternionic multiplication. It is used in the proof that the coarse moduli scheme attached to this moduli problem is integral over $\mathbb{C}$ in the squarefree-level situation, and it is stated relative to hypotheses packaging the uniformisation ($\mathrm{latt}$, $e$), the Hom-as-homothety description, and the two level-structure readings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_iff_exists_smul_latt_eq_and_smul_lattLev_eq_and_smul_lattK_eq_of_pointEquiv.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_iff_exists_smul_latt_eq_and_smul_lattLev_eq_and_smul_lattK_eq_of_pointEquiv
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)

    (latt : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
    (e : ∀ E : FakeEllipticCurve Λ N ℂ,
      SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))

    (hL1 : ∀ E : FakeEllipticCurve Λ N ℂ,
        (∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), latt E = Submodule.span ℤ (Set.range b₀)) ∧
        (∀ x ∈ Λ, ∀ v ∈ latt E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ latt E))

    (hE1 : ∀ (E : FakeEllipticCurve Λ N ℂ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
        e E (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e E P + e E Q)

    (hE2 : ∀ (E : FakeEllipticCurve Λ N ℂ) (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
        e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
        e E (pushPt (E.act x) (E.act_over x) P) =
          ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))
    (hH1 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
        mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
      (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) →
      ∃ c : ℂ, (∀ v ∈ latt E, c • v ∈ latt E') ∧
        ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
          e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
          e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))
    (hH2 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (c : ℂ), (∀ v ∈ latt E, c • v ∈ latt E') →
      ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
        ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
          e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
          e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))
    (hH3 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ ψ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E'.f = E.f),
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f, mapPt φ hφ P = mapPt ψ hψ P) → φ = ψ)

    (lattLev : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
    (hLev : ∀ E : FakeEllipticCurve Λ N ℂ,
      (∀ v : Fin 2 → ℂ, v ∈ lattLev E ↔
        ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
          FactorsThrough E.lev P ∧ e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ∧
      latt E ≤ lattLev E ∧
      (∀ x ∈ Λ, ∀ v ∈ lattLev E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ lattLev E) ∧
      (∀ v ∈ lattLev E, (N : ℤ) • v ∈ latt E) ∧
      (latt E).toAddSubgroup.relIndex (lattLev E).toAddSubgroup = N ^ 2)

    (ℓ : ℕ) (lattK : FakeEllipticCurve.WithExtraLevel Λ N ℓ ℂ → Submodule ℤ (Fin 2 → ℂ))
    (hLK : ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ ℂ) (v : Fin 2 → ℂ),
      v ∈ lattK u ↔ FactorsThrough u.2.levK ((e u.1).symm (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup))) :
    (∀ u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ ℂ,
        FakeEllipticCurve.WithExtraLevel.Iso u u' ↔
          ∃ c : ℂ, c ≠ 0 ∧ c • latt u.1 = latt u'.1 ∧ c • lattLev u.1 = lattLev u'.1 ∧ c • lattK u = lattK u') := by sorry
