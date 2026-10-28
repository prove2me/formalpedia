-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_left_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.left_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:58.124456+00:00
-- url     : https://prove2.me/theorems/c566f708-2c66-4897-9b50-0fec5151fb47
-- title:
--   Selected-floor prefix certificate for prepared pair 19, left list, part 2
-- statement:
--   For prepared pair 19, left list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 24 through 35, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft19_000Part02.lean, lines 11-16, SHA-256 3a2696e06a07c61217b7409e16c8b1a5ee3f558ab435cc9d0ba80796e88b5801. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.left_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 12
      (PairLightPrepared19.leftCached.drop 24)
      (PairLightPrepared19.leftRows.drop 24) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
