-- Prove2me | Theorems.Thm_ArtinKP_C5_norm_upart_le
-- name    : ArtinKP.C5.norm_upart_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:42:36.884244+00:00
-- url     : https://prove2.me/theorems/7703572a-291a-489b-bb75-87c795c7e0e2
-- title:
--   ArtinKP.C5.norm_upart_le: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.C5`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B`):
--
--   ```lean
--   theorem norm_upart_le (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re) {Bd : ℝ}
--       (hB0 : 0 ≤ Bd) (hB : ∀ p : PairClass (RO.SOf 𝔪), ‖wt h𝔪 Ψ s p‖ ≤ Bd) (Q : X F) :
--       ‖upart Ψ s Q‖ ≤ Bd * G (RO.SOf 𝔪) s.re Q
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.RO.SOf` and `ArtinKP.S.TSection` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.X.X` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.B1.G`, `ArtinKP.B1.PairClass`, `ArtinKP.C5.upart` and `ArtinKP.C5.wt` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The proofs of `ArtinKP.N.coeff_resPart_add_hInt` and `ArtinKP.N.integral_box_theta_eq_of_tendsto_ray` of this split import it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
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
import Definitions.Def_ArtinKPB015

section

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C5

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

variable [IsTotallyComplex F]

theorem norm_upart_le (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re) {Bd : ℝ}
    (hB0 : 0 ≤ Bd) (hB : ∀ p : PairClass (RO.SOf 𝔪), ‖wt h𝔪 Ψ s p‖ ≤ Bd) (Q : X F) :
    ‖upart Ψ s Q‖ ≤ Bd * G (RO.SOf 𝔪) s.re Q := by
  sorry

end

end ArtinKP.C5
end
