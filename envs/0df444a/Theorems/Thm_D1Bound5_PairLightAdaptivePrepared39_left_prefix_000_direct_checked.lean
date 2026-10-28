-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_000_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.left_prefix_000_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:00.431411+00:00
-- url     : https://prove2.me/theorems/172abd82-589e-4a95-9fb3-a4603db961b2
-- title:
--   Selected-floor prefix certificate for prepared pair 39, left list
-- statement:
--   For prepared pair 39, left list, the selected-floor certificate succeeds for at most `97` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`.
-- source:
--   D1Bound5/SmallPairLightLeft39Prefix000.lean, lines 16-69, SHA-256 ea39e4dbbd15e490dc6c98a3ad6eed4c24e22544048c02e1de9acda9fb2a9d1d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared39.left_prefix_000_direct_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 97
      (PairLightPrepared39.leftCached.drop 0) (PairLightPrepared39.leftRows.drop 0) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared39
end
