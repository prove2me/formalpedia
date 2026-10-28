-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_left_prefix_002_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.left_prefix_002_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:50.639804+00:00
-- url     : https://prove2.me/theorems/137fca79-d410-4427-b5f5-25408f0949dc
-- title:
--   Selected-floor prefix certificate for prepared pair 19, left list, part 7
-- statement:
--   For prepared pair 19, left list, part 7, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 416 through 439, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft19_002Part07.lean, lines 11-16, SHA-256 cc9209e5bb338891e64a8e612d44502db492b9c1c1806fae980e2596ffd916df. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.left_prefix_002_part07_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.leftCached.drop 416)
      (PairLightPrepared19.leftRows.drop 416) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
