-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:48.808142+00:00
-- url     : https://prove2.me/theorems/01aac643-f44e-4620-8b7e-90e411abcfb7
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list, part 1
-- statement:
--   For prepared pair 4, right list, part 1, the selected-floor certificate succeeds for at most `13` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 84 through 96, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_001Part01.lean, lines 11-16, SHA-256 c4797728ad67d24686631c77d3230986cdc5ed29c88e9931db9811986e39e486. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 13
      (PairLightPrepared4.rightCached.drop 84)
      (PairLightPrepared4.rightRows.drop 84) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
