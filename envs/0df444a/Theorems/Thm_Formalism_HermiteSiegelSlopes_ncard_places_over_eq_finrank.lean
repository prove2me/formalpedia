-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_ncard_places_over_eq_finrank
-- name    : Formalism.HermiteSiegelSlopes.ncard_places_over_eq_finrank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:07.54906+00:00
-- url     : https://prove2.me/theorems/2e8ada02-ae6b-4a99-b303-be9e6014c0c1
-- title:
--   Hermite Siegel Slopes: ncard places over eq finrank
-- statement:
--   The Hermite Siegel Slopes construction uses the ncard places over eq finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L70-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L70-L92

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

theorem Formalism.HermiteSiegelSlopes.ncard_places_over_eq_finrank [IsTotallyComplex F] (v : InfinitePlace F) :
    {w : InfinitePlace E | w.comap (algebraMap F E) = v}.ncard = finrank F E := by sorry
