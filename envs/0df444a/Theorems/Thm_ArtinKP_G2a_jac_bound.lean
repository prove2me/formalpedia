-- Prove2me | Theorems.Thm_ArtinKP_G2a_jac_bound
-- name    : ArtinKP.G2a.jac_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:44:51.291909+00:00
-- url     : https://prove2.me/theorems/3f8a8019-93b0-4306-9ef6-a0ec5c464732
-- title:
--   ArtinKP.G2a.jac_bound: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.G2a`, with `open scoped ComplexConjugate Topology`, `open MeasureTheory Set NumberField Filter`, `open ArtinKP.K ArtinKP.B ArtinKP.RF`):
--
--   ```lean
--   theorem jac_bound (p n₀ : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ ν : ℂ, ν ≠ 0 → ∀ v : ℝ,
--       1 / ((n₀ : ℝ) + 1) ≤ v → v ≤ (n₀ : ℝ) + 1 →
--       ‖ν‖ ^ (2 / 3 : ℝ) * (1 + ‖ν‖) ^ p * ‖jacquet (4 / 3) ν v‖ ≤ K * ((1 + ‖ν‖) ^ 4)⁻¹
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.K.jacquet` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The proof of `ArtinKP.GR.weylFlip_of_thmE` of this split imports it.
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
import Definitions.Def_ArtinKPB015

section

open scoped ComplexConjugate Topology
open MeasureTheory Set NumberField Filter

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.K ArtinKP.B ArtinKP.RF

noncomputable section

theorem jac_bound (p n₀ : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ ν : ℂ, ν ≠ 0 → ∀ v : ℝ,
    1 / ((n₀ : ℝ) + 1) ≤ v → v ≤ (n₀ : ℝ) + 1 →
    ‖ν‖ ^ (2 / 3 : ℝ) * (1 + ‖ν‖) ^ p * ‖jacquet (4 / 3) ν v‖ ≤ K * ((1 + ‖ν‖) ^ 4)⁻¹ := by
  sorry

end

end ArtinKP.G2a
end
