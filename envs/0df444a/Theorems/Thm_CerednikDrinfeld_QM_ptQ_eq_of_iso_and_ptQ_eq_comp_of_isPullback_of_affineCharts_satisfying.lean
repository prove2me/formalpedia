-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_ptQ_eq_of_iso_and_ptQ_eq_comp_of_isPullback_of_affineCharts_satisfying
-- name    : CerednikDrinfeld.QM.ptQ_eq_of_iso_and_ptQ_eq_comp_of_isPullback_of_affineCharts_satisfying
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/f79b75ab-0483-58e0-bde2-384e5911ad05
-- title:
--   Functoriality of the glued point map for QM pairs
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$, maps $\mathrm{star}:\Lambda\to\Lambda$ and $\beta:\mathrm{Fin}\,4\to\Lambda$, a natural number $m$, a commutative ring $\mathcal{O}$, a scheme $M$ with a morphism $\pi_M:M\to\operatorname{Spec}\mathcal{O}$, and a predicate $Q$ on polarised abelian schemes of relative dimension $2$, geometric fibre invariant $36$ and torsion level $m$ over arbitrary commutative rings. Assume: $\mathrm{pt}$ makes $(M,\pi_M)$ a fine moduli scheme for the objects satisfying $Q$ (the point map is constant on isomorphism classes, compatible with base change, surjective and injective up to isomorphism on $\operatorname{Spec}$-valued points); every polarised abelian scheme carrying a `QMStructure` for $(\Lambda,\mathrm{star},\beta)$ — an action of $\Lambda$ on the total space over the base by group-law endomorphisms satisfying the trace condition against $\mathrm{star}$, a section whose $\beta_j$-translates are the marked torsion points, and a polarisation locally isomorphic on the base to the cube of a canonical polarisation datum — satisfies $Q$ ($hQ$); $Q$ is stable under base change of polarised abelian schemes along ring maps ($hQbc$); intersections of two affine opens of $M$ are affine ($hsep$). Fix $f:M_1\to M$, and for each affine open $U\subseteq M$ a polarised abelian scheme $X_U$ over $\Gamma(M,U)$ satisfying $Q$ whose classifying point is $U$'s canonical map $\operatorname{Spec}\Gamma(M,U)\to M$, together with $\zeta_U:Z_U\to\operatorname{Spec}\Gamma(M,U)$ and open immersions $\iota_U:Z_U\to M_1$ making $Z_U$ the fibre product of $f$ and that canonical map. Fix chart point maps $\mathrm{pt}_{Z_U}$ assigning to each ring map $\varphi:\Gamma(M,U)\to T$, each base change $X'$ of $X_U$ along $\varphi$ and each `QMStructure` on $X'$ a morphism $\operatorname{Spec}T\to Z_U$ over $\zeta_U$, subject to: naturality in $T$ along ring maps respecting pullbacks of the structures ($hnat$); invariance under isomorphism of `QMStructure`s over a fixed $T$ ($hiso$); and, for $V\le U$, agreement after composition with $\iota_V$, respectively $\iota_U$, for isomorphic structures over $T$ ($hcompat$). Finally let $\mathrm{pt}_Q$ assign to each commutative ring $S$, each $s:\operatorname{Spec}S\to\operatorname{Spec}\mathcal{O}$, each polarised abelian scheme $X$ over $S$ and each `QMStructure` $t$ on $X$ a morphism $\operatorname{Spec}S\to M_1$ over $f\circ\pi_M$, and assume the chart characterisation $hptQ$: $\mathrm{pt}_Q(X,t)$ followed by $f$ is the classifying point of $\langle X,hQ\rangle$, and for every $\psi:S\to S'$, affine open $U$ and $\varphi:\Gamma(M,U)\to S'$ with $\operatorname{Spec}\varphi$ followed by $U$'s canonical map equal to $\operatorname{Spec}\psi$ followed by that classifying point, for every base change $(X',t')$ of $(X,t)$ along $\psi$ and every base change $X''$ of $X_U$ along $\varphi$ with a `QMStructure` $t''$ isomorphic to $t'$, one has $\operatorname{Spec}\psi$ followed by $\mathrm{pt}_Q(X,t)$ equal to $\mathrm{pt}_{Z_U}(X'',t'')$ followed by $\iota_U$. The conclusion is twofold: $\mathrm{pt}_Q(S,s,X,t)=\mathrm{pt}_Q(S,s,X',t')$ whenever $t$ and $t'$ are isomorphic `QMStructure`s over the same $S$; and for every $\varphi:S\to S'$ and $s,s'$ with $\operatorname{Spec}\varphi$ followed by $s$ equal to $s'$, and every $(X,t)$, $(X',t')$ with $t'$ the pullback of $t$ along $\varphi$, the morphism underlying $\mathrm{pt}_Q(S',s',X',t')$ is $\operatorname{Spec}\varphi$ followed by the morphism underlying $\mathrm{pt}_Q(S,s,X,t)$.
--
--   This verifies the two functoriality axioms — invariance under isomorphism and compatibility with base change — for a point map on pairs (polarised abelian surface, quaternionic multiplication structure) that has been specified only by its behaviour on affine charts of a fine moduli scheme for the objects satisfying a predicate $Q$. It feeds the representability statement [`CerednikDrinfeld.QM.exists_represents_qmStructure_pairs_of_satisfying_isFineModuli_of_qmStructure_of_isUnit_two_of_finiteType`](thm.html#CerednikDrinfeld.QM.exists_represents_qmStructure_pairs_of_satisfying_isFineModuli_of_qmStructure_of_isUnit_two_of_finiteType), which exhibits $M_1$ together with this point map as a fine moduli scheme for the QM moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_ptQ_eq_of_iso_and_ptQ_eq_comp_of_isPullback_of_affineCharts_satisfying.lean

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

theorem CerednikDrinfeld.QM.ptQ_eq_of_iso_and_ptQ_eq_comp_of_isPullback_of_affineCharts_satisfying
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
    (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (X X' : PolarisedAbelianScheme 2 36 m S) (t : QMStructure Λ star β X) (t' : QMStructure Λ star β X'),
        QMStructure.Iso t t' → ptQ S s X t = ptQ S s X' t') ∧
    (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (X : PolarisedAbelianScheme 2 36 m S) (X' : PolarisedAbelianScheme 2 36 m S')
          (t : QMStructure Λ star β X) (t' : QMStructure Λ star β X'),
        QMStructure.IsPullback φ t t' → (ptQ S' s' X' t').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptQ S s X t).1) := by sorry
