-- Prove2me | Theorems.Thm_ArtinKP_F_U_coeff
-- name    : ArtinKP.F.U_coeff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:03:19.575888+00:00
-- url     : https://prove2.me/theorems/ac838eb1-92db-4f67-a79c-487d987cc130
-- title:
--   ArtinKP.F.U_coeff: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.F`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N`, `open Classical in`):
--
--   ```lean
--   theorem U_coeff {T : Finset (SInt 𝔪)} (hT : IsU hG hz6 h g Φ T) {M : ℤ} (hM : 0 ≤ M)
--       (μ : SInt 𝔪) (hV : ValidDepth hG Φ (μ : F) M)
--       (hdeep : ∀ t ∈ T, Small 𝔪 0 ((μ : F) * (t : F) / (g.gen v.asIdeal : F) ^ 3))
--       {D : Set (InfinitePlace F → ℂ)} (hD : PCell (transLat 𝔪 M) D) {n : ℕ}
--       (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) {s : ℂ} (hs : 2 < s.re) (vv : InfinitePlace F → ℝ)
--       (hvv : ∀ w, 0 < vv w) :
--       ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ (3 * s / 2) *
--         ((Ideal.absNorm v.asIdeal : ℂ) ^ (3 - 3 * s)
--           * (∫ x in scaleSet ((g.gen v.asIdeal : F) ^ 3) D,
--               eis ((Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)).twist hG hz6) s
--                 (X.mk x vv hvv) * chiInf ((μ : F) / (g.gen v.asIdeal : F) ^ 3) x)
--           + (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (2 - 3 * s))
--             * (∫ x in scaleSet ((g.gen v.asIdeal : F) ^ 3) D,
--               eis (TSection.restrict v (not_le_of_good h)
--                 ((Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)).twist hG hz6)) s
--                 (X.mk x vv hvv) * chiInf ((μ : F) / (g.gen v.asIdeal : F) ^ 3) x))
--         = ((Ninf ((g.gen v.asIdeal : F) ^ 3) : ℝ) : ℂ) *
--           ((if g.gen v.asIdeal ^ 3 ∣ μ then (Ideal.absNorm v.asIdeal : ℂ) ^ 3 else 0)
--             * ∫ y in D, eis (Φ.twist hG hz6) s
--                 (X.mk y (fun w => vv w / ‖w.embedding ((g.gen v.asIdeal : F) ^ 3)‖)
--                   (fun w => div_pos (hvv w) (norm_pos_iff.2 ((map_ne_zero _).2
--                     (pow_ne_zero 3 (gen_coe_ne_zero h g))))))
--               * chiInf (μ : F) y)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.B.transLat`, `ArtinKP.S.GSection`, `ArtinKP.S.Small` and `ArtinKP.S.GSection.twist` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.FA.not_le_of_good` and `ArtinPrimitiveRoots.C3I.Good` (definitions bundle `ArtinKPB003` of this split); `ArtinKP.X.X.mk` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.B.Ninf`, `ArtinKP.B.ValidDepth`, `ArtinKP.B.chiInf`, `ArtinKP.B.eis` and `ArtinKP.T.PCell` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.F.IsU`, `ArtinKP.F.gen_coe_ne_zero`, `ArtinKP.F.scaleSet`, `ArtinKP.S.GSection.sharp` and `ArtinKP.S.TSection.restrict` (definitions bundle `ArtinKPB017` of this split).
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
  ArtinKP.T ArtinKP.B7 ArtinKP.FA

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F} {v : HeightOneSpectrum (𝓞 F)}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h : C3I.Good 𝔪 v)
  (g : AllowedGen ι 𝔪) (Φ : GSection ι P 𝔪)

open Classical in
include hG hz6 in
theorem U_coeff {T : Finset (SInt 𝔪)} (hT : IsU hG hz6 h g Φ T) {M : ℤ} (hM : 0 ≤ M)
    (μ : SInt 𝔪) (hV : ValidDepth hG Φ (μ : F) M)
    (hdeep : ∀ t ∈ T, Small 𝔪 0 ((μ : F) * (t : F) / (g.gen v.asIdeal : F) ^ 3))
    {D : Set (InfinitePlace F → ℂ)} (hD : PCell (transLat 𝔪 M) D) {n : ℕ}
    (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) {s : ℂ} (hs : 2 < s.re) (vv : InfinitePlace F → ℝ)
    (hvv : ∀ w, 0 < vv w) :
    ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ (3 * s / 2) *
      ((Ideal.absNorm v.asIdeal : ℂ) ^ (3 - 3 * s)
        * (∫ x in scaleSet ((g.gen v.asIdeal : F) ^ 3) D,
            eis ((Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)).twist hG hz6) s
              (X.mk x vv hvv) * chiInf ((μ : F) / (g.gen v.asIdeal : F) ^ 3) x)
        + (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (2 - 3 * s))
          * (∫ x in scaleSet ((g.gen v.asIdeal : F) ^ 3) D,
            eis (TSection.restrict v (not_le_of_good h)
              ((Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)).twist hG hz6)) s
              (X.mk x vv hvv) * chiInf ((μ : F) / (g.gen v.asIdeal : F) ^ 3) x))
      = ((Ninf ((g.gen v.asIdeal : F) ^ 3) : ℝ) : ℂ) *
        ((if g.gen v.asIdeal ^ 3 ∣ μ then (Ideal.absNorm v.asIdeal : ℂ) ^ 3 else 0)
          * ∫ y in D, eis (Φ.twist hG hz6) s
              (X.mk y (fun w => vv w / ‖w.embedding ((g.gen v.asIdeal : F) ^ 3)‖)
                (fun w => div_pos (hvv w) (norm_pos_iff.2 ((map_ne_zero _).2
                  (pow_ne_zero 3 (gen_coe_ne_zero h g))))))
            * chiInf (μ : F) y) := by
  sorry

end

end ArtinKP.F
end
