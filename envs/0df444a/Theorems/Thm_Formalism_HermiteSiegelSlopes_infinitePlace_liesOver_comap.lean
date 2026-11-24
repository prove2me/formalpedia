-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_infinitePlace_liesOver_comap
-- name    : Formalism.HermiteSiegelSlopes.infinitePlace_liesOver_comap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:54.105118+00:00
-- url     : https://prove2.me/theorems/883c9f1b-11ac-4502-83d6-d07b53a48e0f
-- title:
--   Hermite Siegel Slopes: infinite Place lies Over comap
-- statement:
--   The Hermite Siegel Slopes construction uses the infinite Place lies Over comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L65-L68

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

theorem Formalism.HermiteSiegelSlopes.infinitePlace_liesOver_comap (w : InfinitePlace E) : w.LiesOver (w.comap (algebraMap F E)) := by sorry
