-- Prove2me | Theorems.Thm_ArtinKP_C9_exists_theta_bigCell_ne_zero
-- name    : ArtinKP.C9.exists_theta_bigCell_ne_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:54:30.148527+00:00
-- url     : https://prove2.me/theorems/9430572b-71bd-402b-956e-2a749aaf7e9b
-- title:
--   ArtinKP.C9.exists_theta_bigCell_ne_zero: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.C9`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N`):
--
--   ```lean
--   theorem exists_theta_bigCell_ne_zero (hM : 0 ≤ M) :
--       ∃ η ∈ Tc, ∀ (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex],
--         Inv Γ ((bigCell ι P hG hN1 hN η.1 η.2 M 0).twist hG hz6) →
--         theta Γ ((bigCell ι P hG hN1 hN η.1 η.2 M 0).twist hG hz6) ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg`, `ArtinKP.A.Good` and `ArtinKP.A.CubicPkg.IsDeepLevel` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.GSection.twist` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.X.H3`, `ArtinKP.X.X` and `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.X.quotVol` (definitions bundle `ArtinKPB010` of this split); `ArtinKP.X.X.L2` (definitions bundle `ArtinKPB011` of this split); `ArtinKP.C5.Inv` and `ArtinKP.C5.theta` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.S.InClass` and `ArtinKP.S.bigCell` (definitions bundle `ArtinKPB016` of this split).
--
--   **Used by.** The proof of `ArtinKP.GK.hne` of this split imports it.
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

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C9

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

section bigCell

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (M : ℤ) (Tc : Finset {η : F // η ≠ 0})
  (hdisj : ∀ η ∈ Tc, ∀ η' ∈ Tc, η ≠ η' → ∀ c : F, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c)
  (hcov : ∀ c : F, c ≠ 0 → ∃ η ∈ Tc, InClass 𝔪 N η.1 c)

include hdisj hcov in
theorem exists_theta_bigCell_ne_zero (hM : 0 ≤ M) :
    ∃ η ∈ Tc, ∀ (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex],
      Inv Γ ((bigCell ι P hG hN1 hN η.1 η.2 M 0).twist hG hz6) →
      theta Γ ((bigCell ι P hG hN1 hN η.1 η.2 M 0).twist hG hz6) ≠ 0 := by
  sorry

end bigCell

end

end ArtinKP.C9
end
