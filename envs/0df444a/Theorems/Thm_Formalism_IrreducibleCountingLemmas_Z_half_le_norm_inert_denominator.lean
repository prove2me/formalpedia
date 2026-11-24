-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_half_le_norm_inert_denominator
-- name    : Formalism.IrreducibleCountingLemmas.Z.half_le_norm_inert_denominator
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:47:05.979993+00:00
-- url     : https://prove2.me/theorems/03a9c0a8-a427-45b5-9409-142810c540c9
-- title:
--   Z: half le norm inert denominator
-- statement:
--   The Z construction uses the half le norm inert denominator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CardLtAddCardGtAddCardEq.lean#L261-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CardLtAddCardGtAddCardEq.lean#L261-L267

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Topology
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z

theorem Formalism.IrreducibleCountingLemmas.Z.half_le_norm_inert_denominator (q : ℝ) (ch s : ℂ) (hq : 2 ≤ q) (hch : ‖ch‖ = 1) (hs : 1 / 2 < s.re) :
    1 / 2 ≤ ‖1 - ch * ((q ^ 2 : ℝ) : ℂ) ^ (-s)‖ := by sorry
