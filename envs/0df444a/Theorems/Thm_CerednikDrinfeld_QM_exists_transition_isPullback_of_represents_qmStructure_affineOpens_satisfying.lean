-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_transition_isPullback_of_represents_qmStructure_affineOpens_satisfying
-- name    : CerednikDrinfeld.QM.exists_transition_isPullback_of_represents_qmStructure_affineOpens_satisfying
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/d0de5fc2-9264-5475-8fb0-06ab3067eefd
-- title:
--   Cartesian transition maps for QM-structure schemes over affine charts
-- statement:
--   Fix two primes $q,q'$, which occur only as parameters, rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $m\ge 3$, a commutative ring $\mathcal{O}$ in which $m$ is invertible, a map $\star\colon\Lambda\to\Lambda$ and a family $\beta\colon\mathrm{Fin}\,4\to\Lambda$. Let $Q$ be a predicate on polarised abelian schemes of type $(2,36,m)$ over arbitrary commutative rings (a scheme with a commutative relative group law, smooth, proper, with connected fibres of Krull dimension $2$, four $m$-torsion sections independent and spanning the $m$-torsion of geometric fibres, and an invertible module very ample by sections with geometric $H^0$-rank $36$), assumed to hold for every object carrying a `QMStructure` $\Lambda,\star,\beta$ and to be stable under base change along ring homomorphisms. Let $\pi_M\colon M\to\operatorname{Spec}\mathcal{O}$ together with a point map $\mathrm{pt}$ be a fine moduli scheme for the pairs consisting of such an object and a $Q$-witness: $\mathrm{pt}$ is constant on isomorphism classes, compatible with base change, surjective and injective up to isomorphism on $S$-points. For each affine open $U\subseteq M$ let $X_U$ be an object over $\Gamma(M,U)$ satisfying $Q$ whose classifying morphism is the canonical $\operatorname{Spec}\Gamma(M,U)\to M$, and let $\zeta_U\colon Z_U\to\operatorname{Spec}\Gamma(M,U)$ be finite and locally of finite presentation, equipped with a map $\mathrm{pt}^Z_U$ sending a ring homomorphism $\varphi\colon\Gamma(M,U)\to T$, a base change $X'$ of $X_U$ along $\varphi$ and a QM structure on $X'$ to a $T$-point of $Z_U$ over $\operatorname{Spec}\varphi$, this assignment being natural in $(T,\varphi)$ for pullbacks of QM structures, surjective onto such points, and injective in the QM structure. Then there is a family of morphisms $\rho_{UV}\colon Z_U\to Z_V$, indexed by inclusions $U\le V$ of affine opens, with $\rho_{UU}=\mathrm{id}$, $\rho_{UV}$ followed by $\rho_{VW}$ equal to $\rho_{UW}$, such that for each $U\le V$ the square formed by $\rho_{UV}$, the composites $Z_U\to U$ and $Z_V\to V$ obtained from $\zeta_U,\zeta_V$ and the inverse isomorphisms to the spectra, and the open inclusion $U\to V$ is cartesian, and such that $\mathrm{pt}^Z_U$ applied to a QM structure $s'$ on a base change of $X_U$, followed by $\rho_{UV}$, equals $\mathrm{pt}^Z_V$ applied to any isomorphic QM structure $s''$ on a base change of $X_V$ along the corresponding composite homomorphism.
--
--   This supplies the cartesian transition data needed to glue the local schemes $Z_U$, which classify quaternionic multiplication structures on the chart objects, into a single scheme over the fine moduli space of polarised abelian surfaces of type $(2,36,m)$ satisfying $Q$. It is used by [`CerednikDrinfeld.QM.exists_represents_qmStructure_pairs_of_satisfying_isFineModuli_of_qmStructure_of_isUnit_two_of_finiteType`](thm.html#CerednikDrinfeld.QM.exists_represents_qmStructure_pairs_of_satisfying_isFineModuli_of_qmStructure_of_isUnit_two_of_finiteType), where the conclusion serves as the hypothesis block of the general gluing criterion for relative schemes over an affine cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_transition_isPullback_of_represents_qmStructure_affineOpens_satisfying.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem CerednikDrinfeld.QM.exists_transition_isPullback_of_represents_qmStructure_affineOpens_satisfying
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (m : ℕ) (hm : 3 ≤ m)
    (𝒪 : Type) [CommRing 𝒪] (hm' : IsUnit ((m : ℕ) : 𝒪))
    (star : ↥Λ → ↥Λ) (β : Fin (2 * 2) → ↥Λ)
    (Q : ∀ (S : Type) [CommRing S], PolarisedAbelianScheme 2 36 m S → Prop)
    (hQ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X : PolarisedAbelianScheme 2 36 m S), QMStructure Λ star β X → Q S X)
    (hQbc : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (X : PolarisedAbelianScheme 2 36 m S) (X' : PolarisedAbelianScheme 2 36 m S'),
      PolarisedAbelianScheme.IsPullback φ X X' → Q S X → Q S' X')

    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      PolarisedAbelianScheme.Satisfying 2 36 m Q S → SchemeHomOver s πM)
    (hM : PolarisedAbelianScheme.Satisfying.IsFineModuli 2 36 m Q M πM pt)

    (XU : ∀ U : M.affineOpens, PolarisedAbelianScheme 2 36 m Γ(M, U))
    (hQU : ∀ U : M.affineOpens, Q Γ(M, U) (XU U))
    (hXU : ∀ U : M.affineOpens, (pt Γ(M, U) (U.2.fromSpec ≫ πM) ⟨XU U, hQU U⟩).1 = U.2.fromSpec)

    (Z : M.affineOpens → Scheme.{0})
    (ζ : ∀ U : M.affineOpens, Z U ⟶ Spec (CommRingCat.of Γ(M, U)))
    (ptZ : ∀ (U : M.affineOpens) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T) (X' : PolarisedAbelianScheme 2 36 m T),
      PolarisedAbelianScheme.IsPullback φ (XU U) X' → QMStructure Λ star β X' →
      SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ζ U))
    (hζ : ∀ U, IsFinite (ζ U) ∧ LocallyOfFinitePresentation (ζ U))
    (hnat : ∀ (U : M.affineOpens) (T T' : Type) [CommRing T] [CommRing T'] (φ : Γ(M, U) →+* T) (φ' : Γ(M, U) →+* T')
      (ψ : T →+* T') (hψ : ψ.comp φ = φ')
      (X' : PolarisedAbelianScheme 2 36 m T) (X'' : PolarisedAbelianScheme 2 36 m T')
      (hX' : PolarisedAbelianScheme.IsPullback φ (XU U) X') (hX'' : PolarisedAbelianScheme.IsPullback φ' (XU U) X'')
      (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
      QMStructure.IsPullback ψ s' s'' →
      (ptZ U T' φ' X'' hX'' s'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ U T φ X' hX' s').1)
    (hsurjZ : ∀ (U : M.affineOpens) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T) (X' : PolarisedAbelianScheme 2 36 m T)
      (hX' : PolarisedAbelianScheme.IsPullback φ (XU U) X') (z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ζ U)),
      ∃ s' : QMStructure Λ star β X', ptZ U T φ X' hX' s' = z)
    (hinjZ : ∀ (U : M.affineOpens) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T) (X' : PolarisedAbelianScheme 2 36 m T)
      (hX' : PolarisedAbelianScheme.IsPullback φ (XU U) X') (s' s'' : QMStructure Λ star β X'),
      ptZ U T φ X' hX' s' = ptZ U T φ X' hX' s'' → s' = s'') :
    ∃ (ρ : ∀ {U V : M.affineOpens}, U ≤ V → (Z U ⟶ Z V)),
      (∀ U : M.affineOpens, ρ (le_refl U) = 𝟙 (Z U)) ∧
      (∀ {U V W : M.affineOpens} (h₁ : U ≤ V) (h₂ : V ≤ W), ρ h₁ ≫ ρ h₂ = ρ (h₁.trans h₂)) ∧
      (∀ {U V : M.affineOpens} (h : U ≤ V),
        IsPullback (ρ h) (ζ U ≫ U.2.isoSpec.inv) (ζ V ≫ V.2.isoSpec.inv) (M.homOfLE h)) ∧
      (∀ {U V : M.affineOpens} (h : U ≤ V) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T)
        (X' X'' : PolarisedAbelianScheme 2 36 m T)
        (hX' : PolarisedAbelianScheme.IsPullback φ (XU U) X')
        (hX'' : PolarisedAbelianScheme.IsPullback (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) (XU V) X'')
        (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''), QMStructure.Iso s' s'' →
        (ptZ U T φ X' hX' s').1 ≫ ρ h = (ptZ V T (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) X'' hX'' s'').1) := by sorry
