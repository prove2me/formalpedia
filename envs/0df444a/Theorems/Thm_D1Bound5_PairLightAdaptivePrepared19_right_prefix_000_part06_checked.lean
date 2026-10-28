-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_000_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.right_prefix_000_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:56.477983+00:00
-- url     : https://prove2.me/theorems/d4d874f6-73dd-441a-b925-0b26f3b1fa79
-- title:
--   Selected-floor prefix certificate for prepared pair 19, right list, part 6
-- statement:
--   For prepared pair 19, right list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 72 through 83, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight19_000Part06.lean, lines 11-16, SHA-256 42629b21a59058eb21fe8451eb6af685950986f6ba8cf82861cfe1700c0dee16. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.right_prefix_000_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 12
      (PairLightPrepared19.rightCached.drop 72)
      (PairLightPrepared19.rightRows.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
