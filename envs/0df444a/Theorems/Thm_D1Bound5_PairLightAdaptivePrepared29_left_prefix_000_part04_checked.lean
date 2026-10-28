-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared29.left_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:48.547759+00:00
-- url     : https://prove2.me/theorems/798da1aa-9ee1-43ac-bbe7-fef8c30b3231
-- title:
--   Selected-floor prefix certificate for prepared pair 29, left list, part 4
-- statement:
--   For prepared pair 29, left list, part 4, the selected-floor certificate succeeds for at most `17` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared29.sieve`. Original heads 109 through 125, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft29_000Part04.lean, lines 7-11, SHA-256 65a78a4d73dafdf0104031b75e54d20e204c94c9d9b830039cd4d1be7797da41. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared29.left_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 17
      (leftCached000.drop 109) (leftRows000.drop 109) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared29
end
