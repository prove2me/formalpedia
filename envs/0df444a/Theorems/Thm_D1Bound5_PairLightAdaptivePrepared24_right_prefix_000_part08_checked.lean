-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_prefix_000_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.right_prefix_000_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:42.132772+00:00
-- url     : https://prove2.me/theorems/e93c690b-7781-4125-bffb-552df05b21ab
-- title:
--   Selected-floor prefix certificate for prepared pair 24, right list, part 8
-- statement:
--   For prepared pair 24, right list, part 8, the selected-floor certificate succeeds for at most `5` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 96 through 100, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight24_000Part08.lean, lines 11-16, SHA-256 1f956488c47cce6887b8f15174639f7ebf591e9912c2cd96d98bf72cc2ed4fff. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.right_prefix_000_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 5
      (PairLightPrepared24.rightCached.drop 96)
      (PairLightPrepared24.rightRows.drop 96) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
