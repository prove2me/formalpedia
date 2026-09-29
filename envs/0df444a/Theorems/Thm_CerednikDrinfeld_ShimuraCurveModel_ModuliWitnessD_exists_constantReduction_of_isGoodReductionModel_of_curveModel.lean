-- Prove2me | Theorems.Thm_CerednikDrinfeld_ShimuraCurveModel_ModuliWitnessD_exists_constantReduction_of_isGoodReductionModel_of_curveModel
-- name    : CerednikDrinfeld.ShimuraCurveModel.ModuliWitnessD.exists_constantReduction_of_isGoodReductionModel_of_curveModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/197c019f-c0f8-5203-8c04-f1911a250799
-- title:
--   Constant reduction of a quaternionic Shimura curve at ℓ
-- statement:
--   Let $N$ be a non-zero squarefree natural number, $q,q'$ distinct primes with $q,q'\ge 5$ and $q,q'\nmid N$, and let $D$ be a natural number divisible by $2Nqq'$. Let $a,b\in\mathbb Q$ satisfy `IsIndefiniteRamifiedExactlyAt a b q q'`: $0<a$ or $0<b$, and for each finite place $v$ of $\mathbb Q$ the completion $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra exactly when $v$ lies above $q$ or above $q'$. Let $R$ be an Eichler order of level $N$ in $\mathbb H[\mathbb Q,a,b]$ (an intersection of two maximal orders of relative index $N$), $\iota$ an injective $\mathbb Q$-algebra map into $M_2(\mathbb R)$, and $\Lambda\supseteq R$ a maximal order. Let $M$ be a `ShimuraCurveModel` for $R$, $\iota$ and the family of Hecke sets $\ell\mapsto$ `levelHeckeUSet` $\Lambda\,R\,\ell$ for $\ell\mid N$ and `primeHeckeSet` $R\,\ell$ otherwise, and let $w$ be a `ModuliWitnessD` for $M,\Lambda,N,q,q',D$ whose total space $w.X$ is integral and which is a good-reduction model, meaning $w.\pi_X$ is smooth of relative dimension $1$ over $\mathrm{Spec}$ of the localisation of $\mathbb Z$ away from $D$ and all its geometric fibres are integral. Assume the hypothesis `hpts`: there is a curve model $\mathfrak M$ of $M.\bar F$ over $\overline{\mathbb Q}$ (a smooth proper integral curve with function field $M.\bar F$ and a bijection between closed points and places) together with an isomorphism $e_{\mathfrak M}$ from $\mathfrak M.C$ to the fibre product of $w.\pi_X$ and $w.\bar s$, compatible with the structure maps to $\mathrm{Spec}\,\overline{\mathbb Q}$, carrying each $\overline{\mathbb Q}$-point $x$ to the section $w.\mathrm{pts}$ attached to the place of $x$, and inducing on function fields the map $M.\mathrm{toBar}\circ w.e_F^{-1}$ on germs of sections over all opens. Finally let $\ell$ be a prime not dividing $D$ and $\mathfrak B$ a valuation subring of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $\mathfrak B$. The conclusion asserts the existence of: a morphism $s_{\mathfrak B}:\mathrm{Spec}\,\mathfrak B\to\mathrm{Spec}$ of the localisation away from $D$ whose composite with $\mathrm{Spec}$ of the inclusion $\mathfrak B\hookrightarrow\overline{\mathbb Q}$ is $w.\bar s$; a field $K$ over the residue field $k=k(\mathfrak B)$; a constant reduction $\mathcal R$ of $M.\bar F$ along $\mathfrak B$ with residue field $K$ (a valuation subring of $M.\bar F$ meeting $\overline{\mathbb Q}$ in $\mathfrak B$, a surjective residue map onto $K$ with kernel the maximal ideal, compatible with the residue map of $\mathfrak B$, together with a degree-preserving map on places compatible with divisors of functions); a bijection $\mathrm{ptsk}$ from places of $K/k$ to sections of $w.\pi_X$ over $\mathrm{Spec}$ of the residue map followed by $s_{\mathfrak B}$; and a homomorphism $\mathrm{galk}$ from the decomposition subgroup of $\mathfrak B$ over $\mathbb Q$ to the group of semilinear automorphisms of $K$ over $k$ (pairs of ring automorphisms of $K$ and of $k$ compatible with the structure map), such that: each place $P$ of $M.\bar F/\overline{\mathbb Q}$ has a unique extension of $w.\mathrm{pts}\,P$ to a section over $s_{\mathfrak B}$; for any such extension, its reduction modulo the maximal ideal of $\mathfrak B$ is $\mathrm{ptsk}$ of $\mathcal R.\mathrm{placeMap}\,P$; the base component of $\mathrm{galk}\,s$ is the given action of $s$ on $k$; $\mathrm{ptsk}$ is equivariant for $\mathrm{galk}$ and the induced action on sections; $\mathcal R.\mathrm{placeMap}$ intertwines $M.\mathrm{gal}\,\sigma$ with $\mathrm{galk}\,\sigma$, and $\mathcal R.\mathrm{pic}^0$-map intertwines $M.\mathrm{galJ}\,\sigma$ with $\mathrm{galk}\,\sigma$, for $\sigma$ in the decomposition subgroup; and $\mathcal R.\mathrm{pic}^0$-map is injective on torsion of order prime to $\ell$ in $M.J$.
--
--   This is the specialisation step in the style of Deuring's theory of constant reduction of algebraic function fields: the smooth proper model $w.X$ over $\mathbb Z$ away from $D$ produces, at a place $\mathfrak B$ of $\overline{\mathbb Q}$ above a prime $\ell\nmid D$, a reduction of the geometric function field of the quaternionic Shimura curve to the function field of the special fibre, with matching dictionaries of points, Galois equivariance for the decomposition group, and injectivity on torsion prime to $\ell$ of the induced map on degree-zero divisor classes. It is used in the derivation of the Eichler–Shimura congruence relation for the Jacobian of the Shimura curve from a moduli witness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_ShimuraCurveModel_ModuliWitnessD_exists_constantReduction_of_isGoodReductionModel_of_curveModel.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_DescentIntertwining_v2
import Definitions.Def_CerednikDrinfeld_DescentIntertwiningBase
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_QMModuliPropsD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open CategoryTheory CategoryTheory.Limits NeronModelInfra
open AlgebraicGeometry
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve
open AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical

theorem CerednikDrinfeld.ShimuraCurveModel.ModuliWitnessD.exists_constantReduction_of_isGoodReductionModel_of_curveModel
    {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) (hD : 2 * N * q * q' ∣ D)
    (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hRΛ : R ≤ Λ)
    (M : ShimuraCurveModel R ι (fun ℓ => if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ))
    (w : M.ModuliWitnessD Λ N q q' D) (hgood : w.IsGoodReductionModel)

    [hXint : AlgebraicGeometry.IsIntegral w.X]
    (hpts : ∃ (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) M.Fbar)
        (e𝔐 : Quiver.Hom 𝔐.C (CategoryTheory.Limits.pullback w.πX w.sbar)) (_ : CategoryTheory.IsIso e𝔐),
        CategoryTheory.CategoryStruct.comp e𝔐 (CategoryTheory.Limits.pullback.snd w.πX w.sbar) = 𝔐.toBase ∧
        (∀ x : {p : Quiver.Hom (AlgebraicGeometry.Spec (CommRingCat.of (AlgebraicClosure ℚ))) 𝔐.C //
            CategoryTheory.CategoryStruct.comp p 𝔐.toBase =
              CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of (AlgebraicClosure ℚ)))},
          (w.pts (𝔐.pointEquivPlace x)).1 =
            CategoryTheory.CategoryStruct.comp x.1
              (CategoryTheory.CategoryStruct.comp e𝔐 (CategoryTheory.Limits.pullback.fst w.πX w.sbar))) ∧
        (∀ (U : w.X.Opens) [Nonempty (AlgebraicGeometry.Scheme.Opens.toScheme U)]
          [Nonempty (AlgebraicGeometry.Scheme.Opens.toScheme
            ((TopologicalSpace.Opens.map
              (CategoryTheory.CategoryStruct.comp e𝔐 (CategoryTheory.Limits.pullback.fst w.πX w.sbar)).base).obj U))]
          (t : w.X.presheaf.obj (Opposite.op U)),
          𝔐.ffEquiv.symm (𝔐.C.germToFunctionField
            ((TopologicalSpace.Opens.map
              (CategoryTheory.CategoryStruct.comp e𝔐 (CategoryTheory.Limits.pullback.fst w.πX w.sbar)).base).obj U)
            (((CategoryTheory.CategoryStruct.comp e𝔐 (CategoryTheory.Limits.pullback.fst w.πX w.sbar)).app U).hom t)) =
          M.toBar (w.eF.symm (w.X.germToFunctionField U t))))

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ¬ ℓ ∣ D)
    (𝔅 : ValuationSubring (AlgebraicClosure ℚ)) (h𝔅ℓ : 𝔅.LiesOverPrime ℓ) :
    ∃ (s𝔅 : Spec (CommRingCat.of ↥𝔅) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (_ : Spec.map (CommRingCat.ofHom 𝔅.subtype) ≫ s𝔅 = w.sbar)

      (K : Type) (_ : Field K) (_ : Algebra (IsLocalRing.ResidueField ↥𝔅) K)

      (𝓡 : ConstantReduction 𝔅 M.Fbar K)

      (ptsk : Place (IsLocalRing.ResidueField ↥𝔅) K ≃
        SchemeHomOver (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥𝔅)) ≫ s𝔅) w.πX)

      (galk : ↥(𝔅.decompositionSubgroup ℚ) →* SemilinearAut (IsLocalRing.ResidueField ↥𝔅) K),

      (∀ P : Place (AlgebraicClosure ℚ) M.Fbar, ∃! Pt : SchemeHomOver s𝔅 w.πX,
          (w.pts P).1 = Spec.map (CommRingCat.ofHom 𝔅.subtype) ≫ Pt.1) ∧

      (∀ (P : Place (AlgebraicClosure ℚ) M.Fbar) (Pt : SchemeHomOver s𝔅 w.πX),
          (w.pts P).1 = Spec.map (CommRingCat.ofHom 𝔅.subtype) ≫ Pt.1 →
          (ptsk (𝓡.placeMap P)).1 = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥𝔅)) ≫ Pt.1) ∧

      (∀ s : ↥(𝔅.decompositionSubgroup ℚ), SemilinearAut.baseAut (galk s) =
          MulSemiringAction.toRingAut (↥(𝔅.decompositionSubgroup ℚ)) (IsLocalRing.ResidueField ↥𝔅) s) ∧

      (∀ (s : ↥(𝔅.decompositionSubgroup ℚ)) (Q : Place (IsLocalRing.ResidueField ↥𝔅) K),
          (ptsk (galk s • Q)).1 =
            Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (↥(𝔅.decompositionSubgroup ℚ))
              (IsLocalRing.ResidueField ↥𝔅) s)) ≫ (ptsk Q).1) ∧

      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ 𝔅.decompositionSubgroup ℚ)
          (P : Place (AlgebraicClosure ℚ) M.Fbar), 𝓡.placeMap (M.gal σ • P) = galk ⟨σ, hσ⟩ • 𝓡.placeMap P) ∧

      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ 𝔅.decompositionSubgroup ℚ) (c : M.J),
          𝓡.pic0Map (M.galJ σ c) = galk ⟨σ, hσ⟩ • 𝓡.pic0Map c) ∧

      (∀ n : ℕ, ¬ ℓ ∣ n → ∀ t : M.J, n • t = 0 → 𝓡.pic0Map t = 0 → t = 0) := by sorry
