-- Prove2me | Theorems.Thm_ArtinKP_G1_exists_Kir_classDecomp
-- name    : ArtinKP.G1.exists_Kir_classDecomp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:54:18.948279+00:00
-- url     : https://prove2.me/theorems/383d02f5-8c4b-4813-8358-568d33895acb
-- title:
--   ArtinKP.G1.exists_Kir_classDecomp: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.G1`, with `open scoped ComplexConjugate`, `open NumberField IsDedekindDomain ArtinPrimitiveRoots`, `open ArtinKP.A ArtinKP.S ArtinKP.S2 ArtinKP.E ArtinKP.B7`):
--
--   ```lean
--   theorem exists_Kir_classDecomp (hsm : T.toResFun.SmulOn {s : ℂ | 1 < s.re})
--       (Φ : GSection ι P 𝔪) :
--       ∃ (Tc : Finset {η : F // η ≠ 0}) (w : {η : F // η ≠ 0} → ℂ), ∀ β : F, β ≠ 0 →
--         Kir hG hz6 T Φ β = ∑ η ∈ Tc, Kt (B.psiS hG.ne_bot) hG Φ β η.1 (4 / 3) * w η
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.B.psiS`, `ArtinKP.B7.sAdd`, `ArtinKP.S.GSection` and `ArtinKP.S2.cubicSymbol` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.B.kubota` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.E.Theta`, `ArtinKP.G1.Kir`, `ArtinKP.G1.Kt` and `ArtinKP.E.ResFun.SmulOn` (definitions bundle `ArtinKPB016` of this split).
--
--   **Used by.** The proof of `ArtinKP.G2a.norm_tau_le` of this split imports it.
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
import Definitions.Def_ArtinKPB016

section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2 ArtinKP.E ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

section tau

variable [IsTotallyComplex F] (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (T : Theta (B.kubota (ι := ι) (P := P) hG hz6) (4 / 3 : ℂ))

theorem exists_Kir_classDecomp (hsm : T.toResFun.SmulOn {s : ℂ | 1 < s.re})
    (Φ : GSection ι P 𝔪) :
    ∃ (Tc : Finset {η : F // η ≠ 0}) (w : {η : F // η ≠ 0} → ℂ), ∀ β : F, β ≠ 0 →
      Kir hG hz6 T Φ β = ∑ η ∈ Tc, Kt (B.psiS hG.ne_bot) hG Φ β η.1 (4 / 3) * w η := by
  sorry

end tau

end ArtinKP.G1
end
end
