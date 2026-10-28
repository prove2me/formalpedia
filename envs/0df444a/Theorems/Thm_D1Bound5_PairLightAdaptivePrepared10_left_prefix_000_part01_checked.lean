-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:18:50.594066+00:00
-- url     : https://prove2.me/theorems/0b7c72e1-15f1-4684-b4a4-2b5b116bcb51
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list, part 1
-- statement:
--   For prepared pair 10, left list, part 1, the selected-floor certificate succeeds for at most `11` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 11 through 21, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_000Part01.lean, lines 11-16, SHA-256 a7ed8ffd79516214c48b338bac5d07877ed70c4252f2c722ff1bf360ed3aa142. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 11
      (PairLightPrepared10.leftCached.drop 11)
      (PairLightPrepared10.leftRows.drop 11) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
