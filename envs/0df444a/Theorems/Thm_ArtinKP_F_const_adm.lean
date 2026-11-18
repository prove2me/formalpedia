-- Prove2me | Theorems.Thm_ArtinKP_F_const_adm
-- name    : ArtinKP.F.const_adm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:03:42.262381+00:00
-- url     : https://prove2.me/theorems/c7664f4c-46ce-42a5-9117-da4ffb72447a
-- title:
--   ArtinKP.F.const_adm: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.F`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N`):
--
--   ```lean
--   theorem const_adm {M : ℤ} (hM : 0 ≤ M) (hV : ValidDepth hG Φ ((0 : SInt 𝔪) : F) M)
--       {A : AddSubgroup (InfinitePlace F → ℂ)} (hA : Adm A)
--       {D : Set (InfinitePlace F → ℂ)} (hD : PCell A D) {n : ℕ} (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n)
--       {Γ : Subgroup (SL(2, 𝓞 F))} (hΓ : Inv Γ (Φ.twist hG hz6)) (hAΓ : A ≤ latN Γ)
--       {s : ℂ} (hs : 2 < s.re) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
--       ∫ x in D, eis (Φ.twist hG hz6) s (X.mk x v hv)
--         = (((volume D).toReal : ℝ) : ℂ) * (Φ s 0 1 * ((∏ w, v w : ℝ) : ℂ) ^ s
--             + kap 𝔪 0 * mCoeff hG hz6 Φ s * ((∏ w, v w : ℝ) : ℂ) ^ (2 - s))
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.GSection` and `ArtinKP.S.GSection.twist` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.X.X.mk` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.B.ValidDepth`, `ArtinKP.B.eis`, `ArtinKP.C5.Inv`, `ArtinKP.N.latN`, `ArtinKP.T.PCell` and `ArtinKP.T.kap` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.B.mCoeff` and `ArtinKP.F.Adm` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.F.integral_restrict_scale` of this split imports it.
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

attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.F

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N
  ArtinKP.T

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

section coef

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)

include hG hz6 in
theorem const_adm {M : ℤ} (hM : 0 ≤ M) (hV : ValidDepth hG Φ ((0 : SInt 𝔪) : F) M)
    {A : AddSubgroup (InfinitePlace F → ℂ)} (hA : Adm A)
    {D : Set (InfinitePlace F → ℂ)} (hD : PCell A D) {n : ℕ} (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n)
    {Γ : Subgroup (SL(2, 𝓞 F))} (hΓ : Inv Γ (Φ.twist hG hz6)) (hAΓ : A ≤ latN Γ)
    {s : ℂ} (hs : 2 < s.re) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    ∫ x in D, eis (Φ.twist hG hz6) s (X.mk x v hv)
      = (((volume D).toReal : ℝ) : ℂ) * (Φ s 0 1 * ((∏ w, v w : ℝ) : ℂ) ^ s
          + kap 𝔪 0 * mCoeff hG hz6 Φ s * ((∏ w, v w : ℝ) : ℂ) ^ (2 - s)) := by
  sorry

end coef

end

end ArtinKP.F
end
