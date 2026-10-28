-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_001_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.left_prefix_001_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:42.871902+00:00
-- url     : https://prove2.me/theorems/44bba748-2087-41ca-b72f-f7b52f280eaa
-- title:
--   Selected-floor prefix certificate for prepared pair 7, left list, part 4
-- statement:
--   For prepared pair 7, left list, part 4, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 201 through 224, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft7_001Part04.lean, lines 11-16, SHA-256 f9d5279a809991808411039485f7a39f827ff4944b4895d30295d33d2206f44d. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.left_prefix_001_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 24
      (PairLightPrepared7.leftCached.drop 201)
      (PairLightPrepared7.leftRows.drop 201) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
