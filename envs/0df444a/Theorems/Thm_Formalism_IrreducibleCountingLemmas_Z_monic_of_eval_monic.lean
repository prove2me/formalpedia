-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_monic_of_eval_monic
-- name    : Formalism.IrreducibleCountingLemmas.Z.monic_of_eval_monic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:21.911611+00:00
-- url     : https://prove2.me/theorems/f3f78cb9-effd-46f4-a31e-52f261b270dd
-- title:
--   Z: monic of eval monic
-- statement:
--   The Z construction uses the monic of eval monic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CardLtAddCardGtAddCardEq.lean#L547-L576
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CardLtAddCardGtAddCardEq.lean#L547-L576

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

theorem Formalism.IrreducibleCountingLemmas.Z.monic_of_eval_monic {O X' : Type} [CommRing O] [IsLocalRing O] (T : Subalgebra O (X' → O))
    [IsLocalRing T] (p : T[X]) (h : ∀ x, (p.map (ev T x)).Monic) : p.Monic := by sorry
