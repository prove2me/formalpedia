-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.left_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:18:45.871287+00:00
-- url     : https://prove2.me/theorems/cb090ad8-0d5f-4500-a2ee-1fa1aa624b40
-- title:
--   Selected-floor prefix certificate for prepared pair 39, left list, part 3
-- statement:
--   For prepared pair 39, left list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 36 through 47, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft39_000Part03.lean, lines 11-16, SHA-256 4274254e2ce320eea8d3f33762bd8860b4851aba6782db33f675aa2b8d971705. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.left_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 12
      (PairLightPrepared39.leftCached.drop 36)
      (PairLightPrepared39.leftRows.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
