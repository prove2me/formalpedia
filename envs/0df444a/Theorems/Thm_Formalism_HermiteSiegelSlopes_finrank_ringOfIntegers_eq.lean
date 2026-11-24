-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_finrank_ringOfIntegers_eq
-- name    : Formalism.HermiteSiegelSlopes.finrank_ringOfIntegers_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:15.276153+00:00
-- url     : https://prove2.me/theorems/2302c2da-e0d9-47a3-b238-71644d826a1a
-- title:
--   Hermite Siegel Slopes: finrank ring Of Integers eq
-- statement:
--   The Hermite Siegel Slopes construction uses the finrank ring Of Integers eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L368-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L368-L369

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

theorem Formalism.HermiteSiegelSlopes.finrank_ringOfIntegers_eq : finrank (𝓞 F) (𝓞 E) = finrank F E := by sorry
