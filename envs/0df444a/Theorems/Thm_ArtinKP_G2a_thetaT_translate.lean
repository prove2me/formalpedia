-- Prove2me | Theorems.Thm_ArtinKP_G2a_thetaT_translate
-- name    : ArtinKP.G2a.thetaT_translate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:07:27.332558+00:00
-- url     : https://prove2.me/theorems/750246d2-e5fa-49ee-838c-5b8eb77cb1c3
-- title:
--   ArtinKP.G2a.thetaT_translate: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.G2a`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N`):
--
--   ```lean
--   theorem thetaT_translate (σ : SL(2, SInt 𝔪)) (Φ : GSection ι P 𝔪) (Q : X F) :
--       thetaT hG hz6 (S2.GSection.translate hG σ Φ) Q = thetaT hG hz6 Φ (toF 𝔪 σ⁻¹ • Q)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg`, `ArtinKP.A.Good` and `ArtinKP.A.toF` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.GSection` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.X.X` and `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.S2.GSection.translate` (definitions bundle `ArtinKPB016` of this split); `ArtinKP.G2a.ThmE` and `ArtinKP.G2a.thetaT` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.GR.ThetaM_flip` of this split imports it.
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

attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable {hG : Good 𝔪} {z6 : 𝓞 F} {hz6 : IsPrimitiveRoot z6 6} {g : AllowedGen ι 𝔪}

section

variable (hE : ThmE hG hz6 g P)
  (hdiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 →
    ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)

include hE hdiff

theorem thetaT_translate (σ : SL(2, SInt 𝔪)) (Φ : GSection ι P 𝔪) (Q : X F) :
    thetaT hG hz6 (S2.GSection.translate hG σ Φ) Q = thetaT hG hz6 Φ (toF 𝔪 σ⁻¹ • Q) := by
  sorry

end

end

end ArtinKP.G2a
end
