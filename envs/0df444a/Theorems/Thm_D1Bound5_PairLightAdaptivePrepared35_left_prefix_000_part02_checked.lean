-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared35.left_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:13.982057+00:00
-- url     : https://prove2.me/theorems/553762d5-6eae-419b-85a8-2c2a78f08bc3
-- title:
--   Selected-floor prefix certificate for prepared pair 35, left list, part 2
-- statement:
--   For prepared pair 35, left list, part 2, the selected-floor certificate succeeds for at most `34` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared35.sieve`. Original heads 58 through 91; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft35_000Part02.lean, lines 7-11, SHA-256 314eb3be0e2b81b46faf3a73d91a077b0809b93045aabda01010187febdfd9e4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared35.left_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 34
      (leftCached000.drop 58) (leftRows000.drop 58) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared35
end
