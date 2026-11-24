-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_rpow_neg_two_mul_le_half
-- name    : Formalism.IrreducibleCountingLemmas.Z.rpow_neg_two_mul_le_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:27.591239+00:00
-- url     : https://prove2.me/theorems/d7b8ce2a-f64c-460e-8166-4fd88d227b05
-- title:
--   Z: rpow neg two mul le half
-- statement:
--   The Z construction uses the rpow neg two mul le half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CardLtAddCardGtAddCardEq.lean#L253-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CardLtAddCardGtAddCardEq.lean#L253-L259

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

theorem Formalism.IrreducibleCountingLemmas.Z.rpow_neg_two_mul_le_half (q σ : ℝ) (hq : 2 ≤ q) (hσ : 1 / 2 < σ) : q ^ (-2 * σ) ≤ 1 / 2 := by sorry
