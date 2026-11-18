-- Prove2me | Theorems.Thm_ArtinKP_GR_weylFlip_of_thmE
-- name    : ArtinKP.GR.weylFlip_of_thmE
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:09:14.539634+00:00
-- url     : https://prove2.me/theorems/207660a2-eb89-4df0-8c2f-1b475dd38be8
-- title:
--   ArtinKP.GR.weylFlip_of_thmE: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.GR`, with `open scoped MatrixGroups`, `open NumberField IsDedekindDomain ArtinPrimitiveRoots`, `open ArtinKP.A ArtinKP.S ArtinKP.G2a`):
--
--   ```lean
--   theorem weylFlip_of_thmE {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
--       {ι : F →+* ℂ} {P : CubicPkg F} {hG : Good 𝔪} {z6 : 𝓞 F} {hz6 : IsPrimitiveRoot z6 6}
--       {g : AllowedGen ι 𝔪} (hE : ThmE hG hz6 g P) : WeylFlip (ι := ι) P hG hz6
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.G2a.ThmE` and `ArtinKP.GR.WeylFlip` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.GR.secCut_of_isCyclotomicExtension` of this split imports it.
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

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GR

open ArtinKP.A ArtinKP.S ArtinKP.G2a

noncomputable section

theorem weylFlip_of_thmE {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
    {ι : F →+* ℂ} {P : CubicPkg F} {hG : Good 𝔪} {z6 : 𝓞 F} {hz6 : IsPrimitiveRoot z6 6}
    {g : AllowedGen ι 𝔪} (hE : ThmE hG hz6 g P) : WeylFlip (ι := ι) P hG hz6 := by
  sorry

end

end ArtinKP.GR
end
