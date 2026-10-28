-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.left_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:52.783382+00:00
-- url     : https://prove2.me/theorems/d754a78c-6625-44c3-86d8-a91001b96b46
-- title:
--   Selected-floor prefix certificate for prepared pair 17, left list, part 2
-- statement:
--   For prepared pair 17, left list, part 2, the selected-floor certificate succeeds for at most `100` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Original heads 260 through 359; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft17_001Part02.lean, lines 7-11, SHA-256 c12980f510716dd728cca289dc59b2adf11147625e127cc9204bd1a6d111b1cf. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.left_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 100
      (leftCached001.drop 123) (leftRows001.drop 123) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
