-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared33_left_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared33.left_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:51.053535+00:00
-- url     : https://prove2.me/theorems/38084e2f-2e2a-4cd4-9d3c-221ca6136be7
-- title:
--   Selected-floor prefix certificate for prepared pair 33, left list, part 0
-- statement:
--   For prepared pair 33, left list, part 0, the selected-floor certificate succeeds for at most `28` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared33.sieve`. Original heads 0 through 27; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft33_000Part00.lean, lines 7-11, SHA-256 79bf3dca6c1f55b2cfa4065c059d89e7d908213da4b65acf8f11e535b2e32354. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData33_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared33.left_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared33.sieve 28
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared33
end
