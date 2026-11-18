-- Prove2me | Theorems.Thm_ArtinKP_C5_exists_norm_hpart_le
-- name    : ArtinKP.C5.exists_norm_hpart_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:42:32.876989+00:00
-- url     : https://prove2.me/theorems/867588c2-8d61-4d80-abbc-3f6e410b797d
-- title:
--   ArtinKP.C5.exists_norm_hpart_le: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.C5`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace`, `open MeasureTheory Set NumberField Filter IsDedekindDomain`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.CAbs`):
--
--   ```lean
--   theorem exists_norm_hpart_le (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (M : ℝ) {K : Set (X F)}
--       (hK : IsCompact K) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ M → ∀ Q ∈ K, ‖hpart Ψ s Q‖ ≤ C
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.S.TSection` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.X.H3`, `ArtinKP.X.X` and `ArtinKP.X.H3.instTopologicalSpace` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.C5.hpart` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The proofs of `ArtinKP.F.zPsi_restrict_twist`, `ArtinKP.N2.zRes_congr`, `ArtinKP.N.cf_theta`, `ArtinKP.N.cf_theta_translate`, `ArtinKP.N.differentiableOn_Acoef`, `ArtinKP.N.differentiable_hInt`, `ArtinKP.N.integral_box_theta_eq_of_tendsto_ray`, `ArtinKP.N.tendsto_ray_Acoef`, `ArtinKP.T.differentiableOn_Afun` and `ArtinKP.T.tendsto_ray_Afun` of this split import it.
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

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C5

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.CAbs

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

variable [IsTotallyComplex F]

theorem exists_norm_hpart_le (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (M : ℝ) {K : Set (X F)}
    (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ M → ∀ Q ∈ K, ‖hpart Ψ s Q‖ ≤ C := by
  sorry

end

end ArtinKP.C5
end
