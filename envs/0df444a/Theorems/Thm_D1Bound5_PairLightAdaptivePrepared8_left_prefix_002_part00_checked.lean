-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:07.397891+00:00
-- url     : https://prove2.me/theorems/a1c4e51e-7f4d-43b8-845d-53e151b1c9cb
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 0
-- statement:
--   For prepared pair 8, left list, part 0, the selected-floor certificate succeeds for at most `11` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 121 through 131, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_002Part00.lean, lines 11-16, SHA-256 d9b6897fc1f11fd139ba6a4e540de9b168cf6eb9f4be00c9d466ca62138d058c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_002_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 11
      (PairLightPrepared8.leftCached.drop 121)
      (PairLightPrepared8.leftRows.drop 121) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
