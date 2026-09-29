-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_isFineModuli_one_of_isFineModuli_thetaTypeLocally_of_qmStructure_of_isUnit_two_three_of_finiteType
-- name    : CerednikDrinfeld.QM.exists_isFineModuli_one_of_isFineModuli_thetaTypeLocally_of_qmStructure_of_isUnit_two_three_of_finiteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/f463f038-a615-504a-908b-646e566a583f
-- title:
--   Fine moduli for fake elliptic curves with full level m
-- statement:
--   Fix distinct primes $q' \neq q$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0 < a$ or $0 < b$) and, for each place $v$ of $\mathbb{Q}$, the completion $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $v$ divides $q$ or $q'$. Let $\Lambda$ be a maximal order (an order maximal among orders containing it), let $m \ge 3$, and let $\mathcal{O}$ be a commutative ring of finite type over $\mathbb{Z}$ in which $m$, $2$ and $3$ are units. Let $\mu \in \Lambda$ satisfy $\mu^{2} = -qq'$, let $\star : \Lambda \to \Lambda$ satisfy $\mu \cdot \star x = \bar{x}\mu$ for all $x$, and let $\beta_0,\dots,\beta_3 \in \Lambda$ be such that every element of $\Lambda$ is uniquely an integral combination of the $\beta_j$. Two hypotheses are assumed. First, the existence of a fine moduli scheme $M \to \operatorname{Spec}\mathcal{O}$, with its point map, for polarised abelian schemes of relative dimension $2$, geometric fibre degree $36$ and $m$-torsion framing satisfying `PolarisedAbelianScheme.ThetaTypeLocally ![6, 6]`, whose structure morphism is separated, quasi-compact and locally of finite presentation, on which every finite set of points lies in an affine open, and which admits an immersion into $\operatorname{Proj}$ of a polynomial ring over $\mathcal{O}$ commuting with the projections to $\operatorname{Spec}\mathcal{O}$. Second, relative representability of quaternionic structures: for every finite-type $\mathbb{Z}$-algebra $R$ in which $m$ and $2$ are units and every $X$ a polarised abelian scheme of dimension $2$, degree $36$ and level $m$ over $R$, there are a finite, locally of finite presentation morphism $\zeta : Z \to \operatorname{Spec} R$ and a map sending each `QMStructure Λ star β` on a base change $X'$ of $X$ along $\varphi : R \to T$ to a $T$-point of $Z$ over $\operatorname{Spec}\varphi$, compatible with further base change, surjective onto such points and injective on quaternionic structures. The conclusion asserts the existence of $M_1 \to \operatorname{Spec}\mathcal{O}$ together with a point map assigning to each ring $S$, each $\operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and each pair consisting of a fake elliptic curve over $S$ with $\Lambda$-action and level $1$ together with a full level-$m$ structure an $S$-point of $M_1$, such that `IsFineModuli Λ 1 m` holds (the point map is constant on isomorphism classes, compatible with base change, surjective and injective up to isomorphism) and such that $\pi_1$ is separated, quasi-compact and locally of finite presentation, every finite set of points of $M_1$ lies in an affine open, and $M_1$ carries an immersion into $\operatorname{Proj}$ of a polynomial ring over $\mathcal{O}$ compatible with the projection to $\operatorname{Spec}\mathcal{O}$.
--
--   This is the representability statement for the integral model of the Shimura curve attached to the indefinite quaternion algebra ramified exactly at $q$ and $q'$, in the guise of the moduli problem of fake elliptic curves with full level-$m$ structure, deduced from the corresponding moduli problem for $(6,6)$-theta-type polarised abelian surfaces. It feeds the unconditional form [`CerednikDrinfeld.QM.exists_isFineModuli_one_of_isUnit_two_of_isUnit_three`](thm.html#CerednikDrinfeld.QM.exists_isFineModuli_one_of_isUnit_two_of_isUnit_three), which removes the two hypotheses assumed here.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_isFineModuli_one_of_isFineModuli_thetaTypeLocally_of_qmStructure_of_isUnit_two_three_of_finiteType.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem CerednikDrinfeld.QM.exists_isFineModuli_one_of_isFineModuli_thetaTypeLocally_of_qmStructure_of_isUnit_two_three_of_finiteType
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (m : ℕ) (hm : 3 ≤ m)
    (𝒪 : Type) [CommRing 𝒪] [Algebra.FiniteType ℤ 𝒪] (hm' : IsUnit ((m : ℕ) : 𝒪)) (h2 : IsUnit (2 : 𝒪)) (h3 : IsUnit (3 : 𝒪))
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    [h66 : ∀ i : Fin 2, NeZero ((![6, 6] : Fin 2 → ℕ) i)]
    (hA : ∃ (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪))
      (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        PolarisedAbelianScheme.Satisfying 2 (35 + 1) m (PolarisedAbelianScheme.ThetaTypeLocally ![6, 6]) S → SchemeHomOver s πM),
      PolarisedAbelianScheme.Satisfying.IsFineModuli 2 (35 + 1) m (PolarisedAbelianScheme.ThetaTypeLocally ![6, 6]) M πM pt ∧
      IsSeparated πM ∧ QuasiCompact πM ∧ LocallyOfFinitePresentation πM ∧
      (∀ F : Finset M, ∃ U : M.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
      (∃ (qpn : ℕ) (qpι : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) 𝒪)),
        IsImmersion qpι ∧ qpι ≫ ProjSpace.π 𝒪 qpn = πM))
    (hQM : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit ((m : ℕ) : R) → IsUnit (2 : R) → ∀ X : PolarisedAbelianScheme 2 36 m R,
      ∃ (Z : Scheme.{0}) (ζ : Z ⟶ Spec (CommRingCat.of R))
        (ptZ : ∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 36 m T),
        PolarisedAbelianScheme.IsPullback φ X X' → QMStructure Λ star β X' →
        SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ),
        IsFinite ζ ∧ LocallyOfFinitePresentation ζ ∧

        (∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : R →+* T) (φ' : R →+* T') (ψ : T →+* T')
        (hψ : ψ.comp φ = φ')
        (X' : PolarisedAbelianScheme 2 36 m T) (X'' : PolarisedAbelianScheme 2 36 m T')
        (hX' : PolarisedAbelianScheme.IsPullback φ X X') (hX'' : PolarisedAbelianScheme.IsPullback φ' X X'')
        (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
        QMStructure.IsPullback ψ s' s'' →
        (ptZ T' φ' X'' hX'' s'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ T φ X' hX' s').1) ∧

        (∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 36 m T)
        (hX' : PolarisedAbelianScheme.IsPullback φ X X') (z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ),
        ∃ s' : QMStructure Λ star β X', ptZ T φ X' hX' s' = z) ∧

        (∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 36 m T)
        (hX' : PolarisedAbelianScheme.IsPullback φ X X') (s' s'' : QMStructure Λ star β X'),
        ptZ T φ X' hX' s' = ptZ T φ X' hX' s'' → s' = s'')) :
    ∃ (M₁ : Scheme.{0}) (π₁ : M₁ ⟶ Spec (CommRingCat.of 𝒪))
      (ptF₁ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        FakeEllipticCurve.WithFullLevel Λ 1 m S → SchemeHomOver s π₁),
      IsFineModuli Λ 1 m M₁ π₁ ptF₁ ∧
      IsSeparated π₁ ∧ QuasiCompact π₁ ∧ LocallyOfFinitePresentation π₁ ∧
      (∀ F : Finset M₁, ∃ U : M₁.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
      (∃ (qpn : ℕ) (qpι : M₁ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) 𝒪)),
        IsImmersion qpι ∧ qpι ≫ ProjSpace.π 𝒪 qpn = π₁) := by sorry
