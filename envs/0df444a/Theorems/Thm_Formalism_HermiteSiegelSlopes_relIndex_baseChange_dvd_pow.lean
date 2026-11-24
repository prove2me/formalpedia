-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_relIndex_baseChange_dvd_pow
-- name    : Formalism.HermiteSiegelSlopes.relIndex_baseChange_dvd_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:22.62413+00:00
-- url     : https://prove2.me/theorems/d388db31-e64a-4efe-bb83-2e3672877593
-- title:
--   Hermite Siegel Slopes: rel Index base Change dvd pow
-- statement:
--   The Hermite Siegel Slopes construction uses the rel Index base Change dvd pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L443-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L443-L448

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem Formalism.HermiteSiegelSlopes.relIndex_baseChange_dvd_pow {A B : Submodule (𝓞 F) (ι → F)} (hAB : A ≤ B) (hB : B.FG) :
    (bcLat (E := E) A).toAddSubgroup.relIndex (bcLat (E := E) B).toAddSubgroup ∣
      (A.toAddSubgroup.relIndex B.toAddSubgroup) ^ finrank F E := by sorry
