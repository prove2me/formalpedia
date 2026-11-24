-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_circle_pow_surjective
-- name    : Formalism.IrreducibleCountingLemmas.Z.circle_pow_surjective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:38.078703+00:00
-- url     : https://prove2.me/theorems/557da6db-a244-4108-a645-eb2a27a769ec
-- title:
--   Z: circle pow surjective
-- statement:
--   The Z construction uses the circle pow surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZCircleCharExtends.lean#L5-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZCircleCharExtends.lean#L5-L12

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z

theorem Formalism.IrreducibleCountingLemmas.Z.circle_pow_surjective {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun a : Circle => a ^ n) := by sorry
