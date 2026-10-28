-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.right_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:43.42446+00:00
-- url     : https://prove2.me/theorems/395c55c6-dcb2-4de6-a434-4bb1e86ba03c
-- title:
--   Selected-floor prefix certificate for prepared pair 10, right list, part 2
-- statement:
--   For prepared pair 10, right list, part 2, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 97 through 110, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight10_001Part02.lean, lines 11-16, SHA-256 61f4b983d8412fdf7494cc59bdfe3ae9f340f1e7e1f7eb5cee4b3dfe0e848387. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.right_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 14
      (PairLightPrepared10.rightCached.drop 97)
      (PairLightPrepared10.rightRows.drop 97) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
