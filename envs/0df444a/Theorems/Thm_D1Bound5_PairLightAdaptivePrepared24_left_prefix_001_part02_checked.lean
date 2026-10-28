-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_left_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.left_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:41.466858+00:00
-- url     : https://prove2.me/theorems/10705f53-c6c4-4e65-a410-5acc682fd688
-- title:
--   Selected-floor prefix certificate for prepared pair 24, left list, part 2
-- statement:
--   For prepared pair 24, left list, part 2, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 149 through 172, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft24_001Part02.lean, lines 11-16, SHA-256 0bb34002de6c5b1ec76acc77e6243b05ce9777ebb9d5a897dfe6fc254a7a92ef. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.left_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.leftCached.drop 149)
      (PairLightPrepared24.leftRows.drop 149) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
