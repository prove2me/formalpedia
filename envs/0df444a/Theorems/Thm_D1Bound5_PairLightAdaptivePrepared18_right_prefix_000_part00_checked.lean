-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_right_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared18.right_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:00.818242+00:00
-- url     : https://prove2.me/theorems/7c67abe0-79ba-4111-b7e0-5fa6df78557b
-- title:
--   Selected-floor prefix certificate for prepared pair 18, right list, part 0
-- statement:
--   For prepared pair 18, right list, part 0, the selected-floor certificate succeeds for at most `35` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared18.sieve`. Original heads 0 through 34; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight18_000Part00.lean, lines 7-11, SHA-256 91ab4797c2c93ec83be6b30a12db57549fea458fd78ac18b57b14f48c0b7018e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData18_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared18.right_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 35
      (rightCached000.drop 0) (rightRows000.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared18
end
