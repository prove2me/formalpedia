-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_004_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_004_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:32.694605+00:00
-- url     : https://prove2.me/theorems/560dd6ea-1ab5-4a37-b177-a3c835cfe7c3
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list, part 1
-- statement:
--   For prepared pair 8, right list, part 1, the selected-floor certificate succeeds for at most `16` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 289 through 304, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_004Part01.lean, lines 11-16, SHA-256 467ed3747bbe336f7690e8012ac03fb7236db8562f5325225a3e245431e31ced. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_004_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 16
      (PairLightPrepared8.rightCached.drop 289)
      (PairLightPrepared8.rightRows.drop 289) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
