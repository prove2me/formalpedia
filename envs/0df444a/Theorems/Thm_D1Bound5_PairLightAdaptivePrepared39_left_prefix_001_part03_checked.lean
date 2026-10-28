-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.left_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:03.733819+00:00
-- url     : https://prove2.me/theorems/bee912a0-158e-4d32-8b15-86980b66f46a
-- title:
--   Selected-floor prefix certificate for prepared pair 39, left list, part 3
-- statement:
--   For prepared pair 39, left list, part 3, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 169 through 192, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft39_001Part03.lean, lines 11-16, SHA-256 904c743e0fefba653c7a983b23cef88e474172f94f01f694cc19b29e39dec3ed. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.left_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.leftCached.drop 169)
      (PairLightPrepared39.leftRows.drop 169) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
