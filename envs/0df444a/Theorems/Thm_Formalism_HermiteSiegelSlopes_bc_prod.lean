-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_bc_prod
-- name    : Formalism.HermiteSiegelSlopes.bc_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:50.568846+00:00
-- url     : https://prove2.me/theorems/b5cb0f16-a809-4625-9aa1-5ba0129f0ef0
-- title:
--   Hermite Siegel Slopes: bc prod
-- statement:
--   The Hermite Siegel Slopes construction uses the bc prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L94-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L94-L107

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

theorem Formalism.HermiteSiegelSlopes.bc_prod [IsTotallyComplex F] [IsTotallyComplex E] (g : InfinitePlace F → ℝ) :
    ∏ w : InfinitePlace E, g (w.comap (algebraMap F E)) = (∏ v, g v) ^ finrank F E := by sorry
