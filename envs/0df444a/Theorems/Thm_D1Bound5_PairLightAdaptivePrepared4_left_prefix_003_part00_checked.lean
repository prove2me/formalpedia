-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_003_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_003_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:43.743495+00:00
-- url     : https://prove2.me/theorems/e772f06d-8ac8-46eb-b6d6-4c39d3466bf1
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 0
-- statement:
--   For prepared pair 4, left list, part 0, the selected-floor certificate succeeds for at most `20` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 255 through 274, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_003Part00.lean, lines 11-16, SHA-256 ddb33679a98d1167c9ab9223f79b456f5176ae1e2bf148f36610f16e54bddbdb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_003_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 20
      (PairLightPrepared4.leftCached.drop 255)
      (PairLightPrepared4.leftRows.drop 255) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
