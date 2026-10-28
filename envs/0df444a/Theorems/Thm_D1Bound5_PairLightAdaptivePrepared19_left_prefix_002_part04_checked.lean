-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_left_prefix_002_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.left_prefix_002_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:14.032668+00:00
-- url     : https://prove2.me/theorems/79b6adfe-6f3c-4d9a-9307-409e26a94cdb
-- title:
--   Selected-floor prefix certificate for prepared pair 19, left list, part 4
-- statement:
--   For prepared pair 19, left list, part 4, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 344 through 367, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft19_002Part04.lean, lines 11-16, SHA-256 349940d65a489c9a371fb08f2406587cc1e5aa182bf99466873121004e2c59f8. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.left_prefix_002_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.leftCached.drop 344)
      (PairLightPrepared19.leftRows.drop 344) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
