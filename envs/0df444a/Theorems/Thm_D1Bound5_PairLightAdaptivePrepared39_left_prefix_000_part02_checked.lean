-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.left_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:08.783163+00:00
-- url     : https://prove2.me/theorems/cf33304a-e935-4d63-951a-706b86b419c2
-- title:
--   Selected-floor prefix certificate for prepared pair 39, left list, part 2
-- statement:
--   For prepared pair 39, left list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 24 through 35, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft39_000Part02.lean, lines 11-16, SHA-256 b01d5ab8b55dc976942e58e9e7b6a3661b43a68bf85ee623448e5d62c394eed3. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.left_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 12
      (PairLightPrepared39.leftCached.drop 24)
      (PairLightPrepared39.leftRows.drop 24) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
