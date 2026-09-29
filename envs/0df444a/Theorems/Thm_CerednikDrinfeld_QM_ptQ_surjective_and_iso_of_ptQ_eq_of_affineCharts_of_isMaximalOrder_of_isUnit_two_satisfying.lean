-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_ptQ_surjective_and_iso_of_ptQ_eq_of_affineCharts_of_isMaximalOrder_of_isUnit_two_satisfying
-- name    : CerednikDrinfeld.QM.ptQ_surjective_and_iso_of_ptQ_eq_of_affineCharts_of_isMaximalOrder_of_isUnit_two_satisfying
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/4dd9c5a4-3eaf-5853-b3a4-82ef7742733a
-- title:
--   Representability of QM structures from the affine charts
-- statement:
--   Fix distinct primes $q,q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ has $0<a$ or $0<b$ and is, at each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, a division algebra over the completion exactly when $v$ lies above $q$ or $q'$; let $\Lambda$ be a maximal order (an order containing $1$, closed under multiplication, $\mathbb{Q}$-spanning and finitely generated, maximal among such), $\mu\in\Lambda$ with $\mu^2=-(qq')\cdot 1$, $\mathrm{star}:\Lambda\to\Lambda$ satisfying $\mu\,\mathrm{star}(x)=\bar x\mu$, and $\beta:\mathrm{Fin}\,4\to\Lambda$. Let $m\ge 3$, let $\mathcal{O}$ be a commutative ring, $Q$ a predicate on polarised abelian schemes of relative dimension $2$, geometric fibre rank $36$ and level $m$, and let $(M,\pi_M,\mathrm{pt})$ be a fine moduli scheme over $\operatorname{Spec}\mathcal{O}$ for the objects satisfying $Q$ ($\mathrm{pt}$ constant on isomorphism classes, compatible with base change, surjective on points and injective up to isomorphism). Assume: every object carrying a `QMStructure` $\Lambda,\mathrm{star},\beta$ satisfies $Q$; $Q$ is stable under base change; intersections of affine opens of $M$ are affine; $m$ and $2$ are invertible in each $\Gamma(M,U)$. Let $f:M_1\to M$, tautological chart objects $X_U$ over $\Gamma(M,U)$ satisfying $Q$ and classified by $U$'s canonical map, open immersions $\iota_U:Z_U\hookrightarrow M_1$ cartesian over $U$ via $\zeta_U$ and jointly surjective on points, and chart point maps $\mathrm{pt}_{Z_U}$ sending a QM structure on a pullback of $X_U$ to a $\zeta_U$-point, natural in the base ring, constant on isomorphism classes, compatible along inclusions $V\le U$, surjective on points and injective in the QM structure. Let $\mathrm{pt}_Q$ assign to each $S$, each $s:\operatorname{Spec}S\to\operatorname{Spec}\mathcal{O}$ and each pair $(X,t)$ of an object over $S$ and a QM structure on it a point of $M_1$ over $s$, such that $\mathrm{pt}_Q(X,t)$ followed by $f$ is $\mathrm{pt}(X)$, and such that on each chart $\mathrm{pt}_Q$ is computed by $\mathrm{pt}_{Z_U}$ followed by $\iota_U$ in the manner spelled out by the chart characterisation. Then $\mathrm{pt}_Q$ is surjective: every $\operatorname{Spec}S$-point of $M_1$ over $s$ is $\mathrm{pt}_Q(X,t)$ for some $X$ and QM structure $t$; and $\mathrm{pt}_Q(X,t)=\mathrm{pt}_Q(X',t')$ implies that $t$ and $t'$ are isomorphic QM structures.
--
--   This is the gluing step showing that a point map assembled from the affine charts of $M$ makes $M_1$ a fine moduli scheme for polarised abelian surfaces with quaternionic multiplication by $\Lambda$ (the integral model of the Shimura curve attached to the indefinite quaternion algebra ramified exactly at $q$ and $q'$). It is used in the construction of the representing scheme for QM structures over a finite-type base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_ptQ_surjective_and_iso_of_ptQ_eq_of_affineCharts_of_isMaximalOrder_of_isUnit_two_satisfying.lean

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

theorem CerednikDrinfeld.QM.ptQ_surjective_and_iso_of_ptQ_eq_of_affineCharts_of_isMaximalOrder_of_isUnit_two_satisfying
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ)
    {m : ℕ}
    {𝒪 : Type} [CommRing 𝒪] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {Q : ∀ (S : Type) [CommRing S], PolarisedAbelianScheme 2 36 m S → Prop}
    {pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      PolarisedAbelianScheme.Satisfying 2 36 m Q S → SchemeHomOver s πM}
    (hM : PolarisedAbelianScheme.Satisfying.IsFineModuli 2 36 m Q M πM pt)
    (hQ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X : PolarisedAbelianScheme 2 36 m S), QMStructure Λ star β X → Q S X)
    (hQbc : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (X : PolarisedAbelianScheme 2 36 m S) (X' : PolarisedAbelianScheme 2 36 m S'),
      PolarisedAbelianScheme.IsPullback φ X X' → Q S X → Q S' X')
    (hsep : ∀ U V : M.affineOpens, IsAffineOpen ((U : M.Opens) ⊓ (V : M.Opens)))
    {M₁ : Scheme.{0}} (f : M₁ ⟶ M)

    (XU : ∀ U : M.affineOpens, PolarisedAbelianScheme 2 36 m Γ(M, U)) (hQU : ∀ U : M.affineOpens, Q Γ(M, U) (XU U))
    (hXU : ∀ U : M.affineOpens, (pt Γ(M, U) (U.2.fromSpec ≫ πM) ⟨XU U, hQU U⟩).1 = U.2.fromSpec)
    (Z : M.affineOpens → Scheme.{0}) (ζ : ∀ U : M.affineOpens, Z U ⟶ Spec Γ(M, U))
    (ι : ∀ U : M.affineOpens, Z U ⟶ M₁) [∀ U : M.affineOpens, IsOpenImmersion (ι U)]
    (hsq : ∀ U : M.affineOpens, IsPullback (ι U) (ζ U) f U.2.fromSpec)
    (ptZ : ∀ (U : M.affineOpens) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T) (X' : PolarisedAbelianScheme 2 36 m T),
      PolarisedAbelianScheme.IsPullback φ (XU U) X' → QMStructure Λ star β X' →
      SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ζ U))

    (hnat : ∀ (U : M.affineOpens) (T T' : Type) [CommRing T] [CommRing T'] (φ : Γ(M, U) →+* T)
      (φ' : Γ(M, U) →+* T') (ψ : T →+* T') (hψ : ψ.comp φ = φ')
      (X' : PolarisedAbelianScheme 2 36 m T) (X'' : PolarisedAbelianScheme 2 36 m T')
      (hX' : PolarisedAbelianScheme.IsPullback φ (XU U) X') (hX'' : PolarisedAbelianScheme.IsPullback φ' (XU U) X'')
      (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
      QMStructure.IsPullback ψ s' s'' →
      (ptZ U T' φ' X'' hX'' s'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ U T φ X' hX' s').1)

    (hiso : ∀ (U : M.affineOpens) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T) (X' X'' : PolarisedAbelianScheme 2 36 m T)
      (hX' : PolarisedAbelianScheme.IsPullback φ (XU U) X') (hX'' : PolarisedAbelianScheme.IsPullback φ (XU U) X'')
      (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
      QMStructure.Iso s' s'' → (ptZ U T φ X' hX' s').1 = (ptZ U T φ X'' hX'' s'').1)

    (hcompat : ∀ (U V : M.affineOpens) (hVU : (V : M.Opens) ≤ (U : M.Opens)) (T : Type) [CommRing T]
      (φ : Γ(M, V) →+* T) (X' X'' : PolarisedAbelianScheme 2 36 m T)
      (hX' : PolarisedAbelianScheme.IsPullback φ (XU V) X')
      (hX'' : PolarisedAbelianScheme.IsPullback (φ.comp (M.presheaf.map (homOfLE hVU).op).hom) (XU U) X'')
      (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
      QMStructure.Iso s' s'' →
      (ptZ V T φ X' hX' s').1 ≫ ι V = (ptZ U T (φ.comp (M.presheaf.map (homOfLE hVU).op).hom) X'' hX'' s'').1 ≫ ι U)
    (hm : 3 ≤ m) (hmU : ∀ U : M.affineOpens, IsUnit ((m : ℕ) : Γ(M, U)))
    (h2U : ∀ U : M.affineOpens, IsUnit (2 : Γ(M, U)))

    (hιsurj : ∀ x : M₁, ∃ (U : M.affineOpens) (y : Z U), (ι U).base y = x)
    (hsurjZ : ∀ (U : M.affineOpens) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T) (X' : PolarisedAbelianScheme 2 36 m T)
      (hX' : PolarisedAbelianScheme.IsPullback φ (XU U) X') (z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ζ U)),
      ∃ s' : QMStructure Λ star β X', ptZ U T φ X' hX' s' = z)
    (hinjZ : ∀ (U : M.affineOpens) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T) (X' : PolarisedAbelianScheme 2 36 m T)
      (hX' : PolarisedAbelianScheme.IsPullback φ (XU U) X') (s' s'' : QMStructure Λ star β X'),
      ptZ U T φ X' hX' s' = ptZ U T φ X' hX' s'' → s' = s'')

    (ptQ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X : PolarisedAbelianScheme 2 36 m S), QMStructure Λ star β X → SchemeHomOver s (f ≫ πM))
    (hptQ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X : PolarisedAbelianScheme 2 36 m S) (t : QMStructure Λ star β X),
      (ptQ S s X t).1 ≫ f = (pt S s ⟨X, hQ S s X t⟩).1 ∧
      ∀ (S' : Type) [CommRing S'] (ψ : S →+* S') (U : M.affineOpens) (φ : Γ(M, U) →+* S'),
        Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S s ⟨X, hQ S s X t⟩).1 →
        ∀ (X' : PolarisedAbelianScheme 2 36 m S') (t' : QMStructure Λ star β X'),
        PolarisedAbelianScheme.IsPullback ψ X X' → QMStructure.IsPullback ψ t t' →
        ∀ (X'' : PolarisedAbelianScheme 2 36 m S') (hX'' : PolarisedAbelianScheme.IsPullback φ (XU U) X'')
          (t'' : QMStructure Λ star β X''), QMStructure.Iso t' t'' →
        Spec.map (CommRingCat.ofHom ψ) ≫ (ptQ S s X t).1 = (ptZ U S' φ X'' hX'' t'').1 ≫ ι U)
    :
    (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (x : SchemeHomOver s (f ≫ πM)),
        ∃ (X : PolarisedAbelianScheme 2 36 m S) (t : QMStructure Λ star β X), ptQ S s X t = x) ∧
    (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (X X' : PolarisedAbelianScheme 2 36 m S) (t : QMStructure Λ star β X) (t' : QMStructure Λ star β X'),
        ptQ S s X t = ptQ S s X' t' → QMStructure.Iso t t') := by sorry
