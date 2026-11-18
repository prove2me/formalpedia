-- Prove2me | Theorems.Thm_ArtinKP_FB_sum_eInf_reps
-- name    : ArtinKP.FB.sum_eInf_reps
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:06:21.095665+00:00
-- url     : https://prove2.me/theorems/5fea4086-3341-40ea-b379-025288eb61ab
-- title:
--   ArtinKP.FB.sum_eInf_reps: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.FB`, with `open scoped ComplexConjugate Pointwise`, `open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory`, `open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.FA ArtinKP.X ArtinKP.B ArtinKP.B1`, `open Classical in`):
--
--   ```lean
--   theorem sum_eInf_reps [IsTotallyComplex F] (h : C3I.Good 𝔪 v) (g : AllowedGen ι 𝔪) (h𝔪 : 𝔪 ≠ ⊥)
--       (n : ℕ) {T : Finset (SInt 𝔪)} (hT : IsReps (g.gen v.asIdeal ^ n) T) (μ : SInt 𝔪)
--       (hdeep : ∀ t ∈ T, Small 𝔪 0 ((μ : F) * (t : F) / (g.gen v.asIdeal : F) ^ n)) :
--       ∑ t ∈ T, eInf (emb ((μ : F) * (t : F) / (g.gen v.asIdeal : F) ^ n))
--         = if g.gen v.asIdeal ^ n ∣ μ then (Ideal.absNorm v.asIdeal : ℂ) ^ n else 0
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.B.eInf`, `ArtinKP.B1.emb` and `ArtinKP.S.Small` (definitions bundle `ArtinKPB002` of this split); `ArtinPrimitiveRoots.C3I.Good` (definitions bundle `ArtinKPB003` of this split); `ArtinKP.FA.IsReps` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.F.U_coeff` of this split imports it.
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

attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin

set_option autoImplicit false

open scoped ComplexConjugate Pointwise
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.FB

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.FA ArtinKP.X ArtinKP.B ArtinKP.B1

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}

open Classical in
theorem sum_eInf_reps [IsTotallyComplex F] (h : C3I.Good 𝔪 v) (g : AllowedGen ι 𝔪) (h𝔪 : 𝔪 ≠ ⊥)
    (n : ℕ) {T : Finset (SInt 𝔪)} (hT : IsReps (g.gen v.asIdeal ^ n) T) (μ : SInt 𝔪)
    (hdeep : ∀ t ∈ T, Small 𝔪 0 ((μ : F) * (t : F) / (g.gen v.asIdeal : F) ^ n)) :
    ∑ t ∈ T, eInf (emb ((μ : F) * (t : F) / (g.gen v.asIdeal : F) ^ n))
      = if g.gen v.asIdeal ^ n ∣ μ then (Ideal.absNorm v.asIdeal : ℂ) ^ n else 0 := by
  sorry

end ArtinKP.FB
end
end
