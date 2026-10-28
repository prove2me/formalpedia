-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_left_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared12.left_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:51.885595+00:00
-- url     : https://prove2.me/theorems/1cf526f2-80ff-4f37-893d-715c73893966
-- title:
--   Selected-floor prefix certificate for prepared pair 12, left list, part 0
-- statement:
--   For prepared pair 12, left list, part 0, the selected-floor certificate succeeds for at most `29` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared12.sieve`. Original heads 0 through 28; every head retains its complete original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft12_000Part00.lean, lines 7-11, SHA-256 e0d473db134653a332dcf03d93fb17a68ad5e04729ab7623729f0a98fc5e9369. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared12.left_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 29
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared12
end
