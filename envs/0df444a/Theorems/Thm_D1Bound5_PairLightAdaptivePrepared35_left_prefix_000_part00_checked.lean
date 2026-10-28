-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared35.left_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:52.578435+00:00
-- url     : https://prove2.me/theorems/e3f30a15-448a-4622-8d93-c80707855ea4
-- title:
--   Selected-floor prefix certificate for prepared pair 35, left list, part 0
-- statement:
--   For prepared pair 35, left list, part 0, the selected-floor certificate succeeds for at most `28` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared35.sieve`. Original heads 0 through 27; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft35_000Part00.lean, lines 7-11, SHA-256 50ef371a7ba1783a1149c88cae7ae8f7c0cfc163a981c40c6cbcd418808101c1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared35.left_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 28
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared35
end
