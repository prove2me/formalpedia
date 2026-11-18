-- Prove2me | Theorems.Thm_ArtinKP_T_HasCoefT_smulFun
-- name    : ArtinKP.T.HasCoefT.smulFun
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:47:52.183428+00:00
-- url     : https://prove2.me/theorems/b2719352-6d9b-4913-991c-ad934f1f6c0d
-- title:
--   ArtinKP.T.HasCoefT.smulFun: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.T`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N`):
--
--   ```lean
--   theorem HasCoefT.smulFun (h𝔪 : 𝔪 ≠ ⊥) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
--       (h : HasCoefT Ψ ν' a₀ D κ) :
--       HasCoefT (TSection.smulFun f hf Ψ) ν' (fun s => f s * a₀ s) D κ
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.S.TSection` and `ArtinKP.S.TSection.smulFun` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.T.HasCoefT` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The proof of `ArtinKP.GK.theta_per_gen_of_isExterior` of this split imports it.
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
import Definitions.Def_ArtinKPB015

section

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

section coef

variable {Ψ Ψ' : TSection ι 𝔪} {ν' : F} {a₀ b₀ : ℂ → ℂ} {D : Set (InfinitePlace F → ℂ)} {κ : ℂ}

theorem HasCoefT.smulFun (h𝔪 : 𝔪 ≠ ⊥) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h : HasCoefT Ψ ν' a₀ D κ) :
    HasCoefT (TSection.smulFun f hf Ψ) ν' (fun s => f s * a₀ s) D κ := by
  sorry

end coef

end

end ArtinKP.T
end
