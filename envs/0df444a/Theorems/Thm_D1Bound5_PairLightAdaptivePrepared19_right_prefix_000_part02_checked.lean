-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.right_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:31:25.162573+00:00
-- url     : https://prove2.me/theorems/5c3f4ea2-266a-4a21-90d6-2c764f1fb60f
-- title:
--   Selected-floor prefix certificate for prepared pair 19, right list, part 2
-- statement:
--   For prepared pair 19, right list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 24 through 35, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight19_000Part02.lean, lines 11-16, SHA-256 004a24949bd30e406b1b7919184e431e72481edf099f9f0c0d53e1e69c97ac93. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.right_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 12
      (PairLightPrepared19.rightCached.drop 24)
      (PairLightPrepared19.rightRows.drop 24) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
