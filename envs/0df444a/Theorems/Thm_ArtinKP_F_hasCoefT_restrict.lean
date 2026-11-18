-- Prove2me | Theorems.Thm_ArtinKP_F_hasCoefT_restrict
-- name    : ArtinKP.F.hasCoefT_restrict
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:03:39.188196+00:00
-- url     : https://prove2.me/theorems/dfee23e9-6f80-4dc2-bf95-2c8d682d9f22
-- title:
--   ArtinKP.F.hasCoefT_restrict: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.F`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N`, `open Classical in`):
--
--   ```lean
--   theorem hasCoefT_restrict {ν : SInt 𝔪} (hν : ν ≠ 0) {Tr : Finset (SInt 𝔪)}
--       (hT : IsU hG hz6 h g Φ Tr)
--       (hdeep : ∀ t ∈ Tr, Small 𝔪 0
--         (((ν * g.gen v.asIdeal ^ 3 : SInt 𝔪) : F) * (t : F) / (g.gen v.asIdeal : F) ^ 3))
--       {M : ℤ} (hM : 0 ≤ M)
--       (hV : ValidDepth hG Φ ((ν * g.gen v.asIdeal ^ 3 : SInt 𝔪) : F) M)
--       {D : Set (InfinitePlace F → ℂ)} (hD : PCell (transLat 𝔪 M) D) {n : ℕ}
--       (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n)
--       (hc1 : HasCoef hG hz6 Φ (ν * g.gen v.asIdeal ^ 3) D (T.kap 𝔪 0))
--       (hc2 : HasCoef hG hz6 (Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)) ν
--         (scaleSet ((g.gen v.asIdeal : F) ^ 3) D) (T.kap 𝔪 0)) :
--       HasCoefT (TSection.restrict v (not_le_of_good h)
--           ((Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)).twist hG hz6)) (ν : F)
--         (bR hG hz6 h g Φ ν) (scaleSet ((g.gen v.asIdeal : F) ^ 3) D) (T.kap 𝔪 0)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.B.transLat`, `ArtinKP.S.GSection`, `ArtinKP.S.Small` and `ArtinKP.S.GSection.twist` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.FA.not_le_of_good` and `ArtinPrimitiveRoots.C3I.Good` (definitions bundle `ArtinKPB003` of this split); `ArtinKP.B.ValidDepth`, `ArtinKP.T.HasCoef`, `ArtinKP.T.HasCoefT`, `ArtinKP.T.PCell` and `ArtinKP.T.kap` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.F.IsU`, `ArtinKP.F.bR`, `ArtinKP.F.gen_coe_ne_zero`, `ArtinKP.F.scaleSet`, `ArtinKP.S.GSection.sharp` and `ArtinKP.S.TSection.restrict` (definitions bundle `ArtinKPB017` of this split).
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
import Definitions.Def_ArtinKPB017

section

attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.F

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N
  ArtinKP.T ArtinKP.B7 ArtinKP.FA ArtinKP.N2

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F} {v : HeightOneSpectrum (𝓞 F)}

section gen

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h : C3I.Good 𝔪 v)
  (g : AllowedGen ι 𝔪) (Φ : GSection ι P 𝔪)

open Classical in
include hG hz6 in
theorem hasCoefT_restrict {ν : SInt 𝔪} (hν : ν ≠ 0) {Tr : Finset (SInt 𝔪)}
    (hT : IsU hG hz6 h g Φ Tr)
    (hdeep : ∀ t ∈ Tr, Small 𝔪 0
      (((ν * g.gen v.asIdeal ^ 3 : SInt 𝔪) : F) * (t : F) / (g.gen v.asIdeal : F) ^ 3))
    {M : ℤ} (hM : 0 ≤ M)
    (hV : ValidDepth hG Φ ((ν * g.gen v.asIdeal ^ 3 : SInt 𝔪) : F) M)
    {D : Set (InfinitePlace F → ℂ)} (hD : PCell (transLat 𝔪 M) D) {n : ℕ}
    (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n)
    (hc1 : HasCoef hG hz6 Φ (ν * g.gen v.asIdeal ^ 3) D (T.kap 𝔪 0))
    (hc2 : HasCoef hG hz6 (Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)) ν
      (scaleSet ((g.gen v.asIdeal : F) ^ 3) D) (T.kap 𝔪 0)) :
    HasCoefT (TSection.restrict v (not_le_of_good h)
        ((Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)).twist hG hz6)) (ν : F)
      (bR hG hz6 h g Φ ν) (scaleSet ((g.gen v.asIdeal : F) ^ 3) D) (T.kap 𝔪 0) := by
  sorry

end gen

end

end ArtinKP.F
end
