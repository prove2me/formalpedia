-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_schemeHomOver_forall_comp_eq_ptZ_comp_openImmersion_of_affineCharts_satisfying
-- name    : CerednikDrinfeld.QM.exists_schemeHomOver_forall_comp_eq_ptZ_comp_openImmersion_of_affineCharts_satisfying
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/fe673341-19f5-52a4-ae6a-bd6ce60fd56d
-- title:
--   Gluing chart-wise QM point maps over a Q-fine moduli scheme
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$, a map $\mathrm{star}:\Lambda\to\Lambda$, a family $\beta:\mathrm{Fin}\,4\to\Lambda$, a natural number $m$, a commutative ring $\mathcal{O}$, a scheme $M$ with a morphism $\pi_M:M\to\operatorname{Spec}\mathcal{O}$, a predicate $Q$ on polarised abelian schemes of type $(2,36,m)$ over commutative rings (relative dimension $2$, geometric fibre rank $36$, $m$-torsion basis), and an assignment $\mathrm{pt}$ sending a ring $S$, a morphism $s:\operatorname{Spec}S\to\operatorname{Spec}\mathcal{O}$ and a $Q$-satisfying object over $S$ to a morphism $\operatorname{Spec}S\to M$ over $s$. Assume: $(M,\pi_M,\mathrm{pt})$ is a fine moduli datum for the $Q$-satisfying objects, i.e. $\mathrm{pt}$ is constant on isomorphism classes, compatible with base change, surjective on $S$-points of $M$ over $s$, and injective up to isomorphism ($hM$); every polarised abelian scheme carrying a $\mathrm{QMStructure}\ \Lambda\ \mathrm{star}\ \beta$ satisfies $Q$ ($hQ$); $Q$ is preserved by pullback along ring maps ($hQbc$); the intersection of any two affine opens of $M$ is affine ($hsep$). Fix a scheme $M_1$ and $f:M_1\to M$, and for each affine open $U\subseteq M$: an object $X_U$ over $\Gamma(M,U)$ with a $Q$-witness whose classifying morphism is the canonical $\operatorname{Spec}\Gamma(M,U)\to M$ ($hXU$); a scheme $Z_U$ with $\zeta_U:Z_U\to\operatorname{Spec}\Gamma(M,U)$ and an open immersion $\iota_U:Z_U\to M_1$ forming a pullback square over $f$ ($hsq$), so $Z_U$ is $f^{-1}(U)$; and a chart point map $\mathrm{ptZ}$ assigning, to a ring map $\varphi:\Gamma(M,U)\to T$, an object $X'$ over $T$ exhibited as the pullback of $X_U$ along $\varphi$, and a QM structure on $X'$, a morphism $\operatorname{Spec}T\to Z_U$ over $\operatorname{Spec}\varphi$. Assume $\mathrm{ptZ}$ is natural in base change of QM structures along $\psi:T\to T'$ with $\psi\circ\varphi=\varphi'$ ($hnat$), depends only on the isomorphism class of the QM structure ($hiso$), and is compatible along inclusions $V\subseteq U$ of affine opens after composing with $\iota_V$, resp. $\iota_U$ ($hcompat$). Then for every ring $S$, every $s:\operatorname{Spec}S\to\operatorname{Spec}\mathcal{O}$, every polarised abelian scheme $X$ of type $(2,36,m)$ over $S$ and every QM structure $t$ on $X$, there is a morphism $q:\operatorname{Spec}S\to M_1$ over $s$ with respect to $f$ followed by $\pi_M$ such that $q$ followed by $f$ is the classifying morphism of $(X,t)$, and such that for every ring $S'$, ring map $\psi:S\to S'$, affine open $U$ and $\varphi:\Gamma(M,U)\to S'$ with $\operatorname{Spec}\varphi$ followed by $\operatorname{Spec}\Gamma(M,U)\to M$ equal to $\operatorname{Spec}\psi$ followed by that classifying morphism, and for all pullbacks $X'$ of $X$ and $t'$ of $t$ along $\psi$ and all pullbacks $X''$ of $X_U$ along $\varphi$ with a QM structure $t''$ isomorphic to $t'$, one has $\operatorname{Spec}\psi$ followed by $q$ equal to $\mathrm{ptZ}$ of the datum $(U,\varphi,X'',t'')$ followed by $\iota_U$.
--
--   This is the local-to-global step in the statement that a functor relatively representable over a representable functor is itself representable, here for quaternionic-multiplication structures on polarised abelian surfaces over a fine moduli scheme of $Q$-satisfying polarised abelian schemes: the chart-wise point maps on the pullbacks $f^{-1}(U)$ glue to a single point map on $M_1$, characterised by its behaviour after base change into each affine chart. It feeds the construction of the representing morphism for pairs (polarised abelian scheme, QM structure), used in [`CerednikDrinfeld.QM.exists_represents_qmStructure_pairs_of_satisfying_isFineModuli_of_qmStructure_of_isUnit_two_of_finiteType`](thm.html#CerednikDrinfeld.QM.exists_represents_qmStructure_pairs_of_satisfying_isFineModuli_of_qmStructure_of_isUnit_two_of_finiteType).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_schemeHomOver_forall_comp_eq_ptZ_comp_openImmersion_of_affineCharts_satisfying.lean

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

theorem CerednikDrinfeld.QM.exists_schemeHomOver_forall_comp_eq_ptZ_comp_openImmersion_of_affineCharts_satisfying
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (star : ↥Λ → ↥Λ) (β : Fin (2 * 2) → ↥Λ) {m : ℕ}
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

    (XU : ∀ U : M.affineOpens, PolarisedAbelianScheme 2 36 m Γ(M, U))
    (hQU : ∀ U : M.affineOpens, Q Γ(M, U) (XU U))
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
    (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (X : PolarisedAbelianScheme 2 36 m S) (t : QMStructure Λ star β X) :
    ∃ q : SchemeHomOver s (f ≫ πM),
      q.1 ≫ f = (pt S s ⟨X, hQ S s X t⟩).1 ∧
      ∀ (S' : Type) [CommRing S'] (ψ : S →+* S') (U : M.affineOpens) (φ : Γ(M, U) →+* S'),
        Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S s ⟨X, hQ S s X t⟩).1 →
        ∀ (X' : PolarisedAbelianScheme 2 36 m S') (t' : QMStructure Λ star β X'),
        PolarisedAbelianScheme.IsPullback ψ X X' → QMStructure.IsPullback ψ t t' →
        ∀ (X'' : PolarisedAbelianScheme 2 36 m S') (hX'' : PolarisedAbelianScheme.IsPullback φ (XU U) X'')
          (t'' : QMStructure Λ star β X''), QMStructure.Iso t' t'' →
        Spec.map (CommRingCat.ofHom ψ) ≫ q.1 = (ptZ U S' φ X'' hX'' t'').1 ≫ ι U := by sorry
