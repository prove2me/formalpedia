-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_left_prefix_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.left_prefix_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:54.021906+00:00
-- url     : https://prove2.me/theorems/0ee27f26-51f6-4e14-9281-ad8587f3d42c
-- title:
--   Selected-floor prefix certificate for prepared pair 24, left list, part 5
-- statement:
--   For prepared pair 24, left list, part 5, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 221 through 244, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft24_001Part05.lean, lines 11-16, SHA-256 63bb1eba1d367a72f951be4766e7497673f578d5318bff02d7d4512e7d52dae0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.left_prefix_001_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.leftCached.drop 221)
      (PairLightPrepared24.leftRows.drop 221) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
