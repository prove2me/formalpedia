-- Prove2me | Theorems.Thm_ArtinKP_HB_digCoefNu_eq
-- name    : ArtinKP.HB.digCoefNu_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:08:52.148968+00:00
-- url     : https://prove2.me/theorems/29703e1a-7972-4341-9787-340bdde7b2be
-- title:
--   ArtinKP.HB.digCoefNu_eq: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.HB`, with `open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots ArtinKP.A ArtinKP.S`, `open WithZero`, `open scoped Classical`):
--
--   ```lean
--   theorem digCoefNu_eq {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) (v : H.Dig 𝔪 𝔟)
--       (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
--       (hc : γ.1 1 0 = cdig g 𝔟 v)
--       (hd : ((γ.1 1 1 : SInt 𝔪) : F) = -((cdig g 𝔟 v : F) * H.xdig g 𝔟 v))
--       (μ ν : {x : SInt 𝔪 // x ≠ 0})
--       (hν : ((ν : SInt 𝔪) : F) =
--         ((μ : SInt 𝔪) : F) * ((g.gen 𝔟 : F) / (cdig g 𝔟 v : F)) ^ 2) :
--       L3X.coefF' g ⊤ (H0.rowOf h𝔪 g μ) *
--           sAddChar 𝔪 (((μ : SInt 𝔪) : F) * ((γ.1 0 0 : SInt 𝔪) : F) / (cdig g 𝔟 v : F)) *
--           kappa ι 𝔪 γ * brk ι Pk 𝔪 ((μ : SInt 𝔪) : F) (cdig g 𝔟 v : F) =
--         digCoefNu h𝔪 g 𝔟 v ν
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg`, `ArtinKP.A.Good` and `ArtinKP.A.kappa` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.brk` (definitions bundle `ArtinKPB002` of this split); `ArtinPrimitiveRoots.C3I.Good` (definitions bundle `ArtinKPB003` of this split); `ArtinKP.H.Dig`, `ArtinKP.H.xdig`, `ArtinKP.H0.rowOf`, `ArtinKP.HB.cdig`, `ArtinKP.HB.digCoefNu` and `ArtinPrimitiveRoots.L3X.coefF'` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.HB.autCut2_of_secCut` of this split imports it.
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
import Definitions.Def_ArtinKPB017

section

attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero

namespace ArtinKP.HB

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots ArtinKP.A ArtinKP.S
open WithZero

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

section D

variable (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (hgood : ∀ (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hext : IsExterior 𝔪 P),
    C3I.Good 𝔪 (⟨P, hP, hext.1⟩ : HeightOneSpectrum (𝓞 F)))
  (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪)

include hG hz6 hgood

theorem digCoefNu_eq {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) (v : H.Dig 𝔪 𝔟)
    (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
    (hc : γ.1 1 0 = cdig g 𝔟 v)
    (hd : ((γ.1 1 1 : SInt 𝔪) : F) = -((cdig g 𝔟 v : F) * H.xdig g 𝔟 v))
    (μ ν : {x : SInt 𝔪 // x ≠ 0})
    (hν : ((ν : SInt 𝔪) : F) =
      ((μ : SInt 𝔪) : F) * ((g.gen 𝔟 : F) / (cdig g 𝔟 v : F)) ^ 2) :
    L3X.coefF' g ⊤ (H0.rowOf h𝔪 g μ) *
        sAddChar 𝔪 (((μ : SInt 𝔪) : F) * ((γ.1 0 0 : SInt 𝔪) : F) / (cdig g 𝔟 v : F)) *
        kappa ι 𝔪 γ * brk ι Pk 𝔪 ((μ : SInt 𝔪) : F) (cdig g 𝔟 v : F) =
      digCoefNu h𝔪 g 𝔟 v ν := by
  sorry

end D

end

end ArtinKP.HB
end
