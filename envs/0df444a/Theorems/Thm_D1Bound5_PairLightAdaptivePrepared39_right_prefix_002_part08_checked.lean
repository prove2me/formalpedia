-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_002_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.right_prefix_002_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:28.241732+00:00
-- url     : https://prove2.me/theorems/3dced5ee-2e0a-4c53-892a-700dbcdea05e
-- title:
--   Selected-floor prefix certificate for prepared pair 39, right list, part 8
-- statement:
--   For prepared pair 39, right list, part 8, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 428 through 451, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight39_002Part08.lean, lines 11-16, SHA-256 788ef11844c0d1652969bfd3d1fd627b2c55814f41ec841a05d34f061f421a55. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.right_prefix_002_part08_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.rightCached.drop 428)
      (PairLightPrepared39.rightRows.drop 428) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
