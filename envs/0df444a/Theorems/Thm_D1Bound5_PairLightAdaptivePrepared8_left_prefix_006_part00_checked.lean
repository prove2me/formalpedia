-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_006_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_006_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:51.838419+00:00
-- url     : https://prove2.me/theorems/a12dcceb-5a57-424d-b991-fe470ca9be2d
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 0
-- statement:
--   For prepared pair 8, left list, part 0, the selected-floor certificate succeeds for at most `37` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 527 through 563, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_006Part00.lean, lines 11-16, SHA-256 258644644e1cab5784f9b8dac6ec9529ed22cc1d571516a3a1b32b9fa817f331. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_006_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 37
      (PairLightPrepared8.leftCached.drop 527)
      (PairLightPrepared8.leftRows.drop 527) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
