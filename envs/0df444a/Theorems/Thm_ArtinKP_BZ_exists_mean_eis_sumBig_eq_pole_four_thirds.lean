-- Prove2me | Theorems.Thm_ArtinKP_BZ_exists_mean_eis_sumBig_eq_pole_four_thirds
-- name    : ArtinKP.BZ.exists_mean_eis_sumBig_eq_pole_four_thirds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:03:55.154944+00:00
-- url     : https://prove2.me/theorems/81843859-4fe7-42c0-8a27-e3f267762990
-- title:
--   ArtinKP.BZ.exists_mean_eis_sumBig_eq_pole_four_thirds: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.BZ`, with `open scoped MatrixGroups ComplexConjugate`, `open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K ArtinKP.B7 ArtinKP.B`):
--
--   ```lean
--   theorem exists_mean_eis_sumBig_eq_pole_four_thirds (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
--       (hz6 : IsPrimitiveRoot z6 6) :
--       ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 < s.re} ∧
--         G (4 / 3) = (sZetaResidue 𝔪 : ℂ) / (3 * C3P.zetaS 𝔪 2) ∧ G (4 / 3) ≠ 0 ∧
--         ∀ {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (M : ℤ) (T : Finset {η : F // η ≠ 0}),
--           (∀ η ∈ T, ∀ η' ∈ T, η ≠ η' → ∀ c : F, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c) →
--           (∀ c : F, c ≠ 0 → ∃ η ∈ T, InClass 𝔪 N η.1 c) →
--           ∀ {D : Set (InfinitePlace F → ℂ)}, IsAddFundamentalDomain (transLat 𝔪 M) D volume →
--           ∀ {s : ℂ}, 2 < s.re → ∀ (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w),
--             (((volume D).toReal : ℝ) : ℂ)⁻¹
--                 * ∫ x in D, eis ((sumBig ι hG hN1 hN M T).twist hG hz6) s (X.mk x v hv)
--               = ((constC 𝔪 M : ℝ) : ℂ)
--                 * ((Real.pi : ℂ) / (s - 1)) ^ Fintype.card (InfinitePlace F)
--                 * (G s / (s - 4 / 3)) * ((∏ w, v w : ℝ) : ℂ) ^ (2 - s)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg`, `ArtinKP.A.Good` and `ArtinKP.A.CubicPkg.IsDeepLevel` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.B.transLat` and `ArtinKP.S.GSection.twist` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.X.X.mk` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.B.eis` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.S.InClass` (definitions bundle `ArtinKPB016` of this split); `ArtinKP.B.sumBig`, `ArtinKP.BZ.constC` and `ArtinPrimitiveRoots.C3P.zetaS` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.C9.theta_psiSum_ne_zero` of this split imports it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB017

section

attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.BZ

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K ArtinKP.B7 ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable [IsTotallyComplex F]

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (M : ℤ) (T : Finset {η : F // η ≠ 0})
  (hdisj : ∀ η ∈ T, ∀ η' ∈ T, η ≠ η' → ∀ c : F, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c)
  (hcov : ∀ c : F, c ≠ 0 → ∃ η ∈ T, InClass 𝔪 N η.1 c)

theorem exists_mean_eis_sumBig_eq_pole_four_thirds (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 < s.re} ∧
      G (4 / 3) = (sZetaResidue 𝔪 : ℂ) / (3 * C3P.zetaS 𝔪 2) ∧ G (4 / 3) ≠ 0 ∧
      ∀ {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (M : ℤ) (T : Finset {η : F // η ≠ 0}),
        (∀ η ∈ T, ∀ η' ∈ T, η ≠ η' → ∀ c : F, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c) →
        (∀ c : F, c ≠ 0 → ∃ η ∈ T, InClass 𝔪 N η.1 c) →
        ∀ {D : Set (InfinitePlace F → ℂ)}, IsAddFundamentalDomain (transLat 𝔪 M) D volume →
        ∀ {s : ℂ}, 2 < s.re → ∀ (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w),
          (((volume D).toReal : ℝ) : ℂ)⁻¹
              * ∫ x in D, eis ((sumBig ι hG hN1 hN M T).twist hG hz6) s (X.mk x v hv)
            = ((constC 𝔪 M : ℝ) : ℂ)
              * ((Real.pi : ℂ) / (s - 1)) ^ Fintype.card (InfinitePlace F)
              * (G s / (s - 4 / 3)) * ((∏ w, v w : ℝ) : ℂ) ^ (2 - s) := by
  sorry

end ArtinKP.BZ
end
end
