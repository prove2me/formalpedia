-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_001_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.left_prefix_001_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:22:33.150717+00:00
-- url     : https://prove2.me/theorems/ac525d66-7e06-4281-8174-bb740fa08294
-- title:
--   Selected-floor prefix certificate for prepared pair 7, left list, part 6
-- statement:
--   For prepared pair 7, left list, part 6, the selected-floor certificate succeeds for at most `19` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 249 through 267, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft7_001Part06.lean, lines 11-16, SHA-256 8848e20aecdea02d8c03169d2c3b3da73ff60b051f354c0d93ee603cb7798faa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.left_prefix_001_part06_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 19
      (PairLightPrepared7.leftCached.drop 249)
      (PairLightPrepared7.leftRows.drop 249) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
