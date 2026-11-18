-- Prove2me | Theorems.Thm_ArtinKP_GL_eisEigen_of_two_lt_re
-- name    : ArtinKP.GL.eisEigen_of_two_lt_re
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:43:17.234502+00:00
-- url     : https://prove2.me/theorems/5832f3c7-e40d-4ad2-8343-04b5fc43f3d8
-- title:
--   ArtinKP.GL.eisEigen_of_two_lt_re: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.GL`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace`, `open MeasureTheory Set NumberField Filter IsDedekindDomain`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.CAbs ArtinKP.C5`):
--
--   ```lean
--   theorem eisEigen_of_two_lt_re (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re) : EisEigen Ψ s
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.S.TSection` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.C5.EisEigen` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The proofs of `ArtinKP.C9.exists_theta_bigCell_ne_zero`, `ArtinKP.C9.theta_eq_zero_of_forall_tau_eq_zero`, `ArtinKP.C9.theta_psiSum_ne_zero`, `ArtinKP.F.tendsto_mext_zPsi`, `ArtinKP.F.zPsi_add`, `ArtinKP.F.zPsi_restrict_twist`, `ArtinKP.F.zPsi_smul`, `ArtinKP.F.zPsi_translate_nMat`, `ArtinKP.G2a.integral_strip_term`, `ArtinKP.G2a.thetaS_smul_gammaN`, `ArtinKP.G2a.thetaT_translate`, `ArtinKP.GK.hne`, `ArtinKP.GK.kw_theta_of_diffInS`, `ArtinKP.N2.cusp_integral_eq_zero`, `ArtinKP.N2.theta_eq_zero_iff_forall_zPsi_translate_eq_zero`, `ArtinKP.N2.zRes_congr`, `ArtinKP.T.hasResOn_kubota_aSer`, `ArtinKP.T.integral_theta_of_hasCoefT`, `ArtinKP.T.resSlit_add_of_seed` and `ArtinKP.T.resSlit_mul_of_seed` of this split import it.
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

namespace ArtinKP.GL

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.CAbs ArtinKP.C5

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}
variable [IsTotallyComplex F]

theorem eisEigen_of_two_lt_re (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re) : EisEigen Ψ s := by
  sorry

end

end ArtinKP.GL
end
