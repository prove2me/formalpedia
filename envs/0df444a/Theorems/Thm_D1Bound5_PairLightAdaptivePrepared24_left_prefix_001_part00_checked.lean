-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_left_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.left_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:02:11.033769+00:00
-- url     : https://prove2.me/theorems/253fd177-6012-4986-9913-f4a6bb54fd27
-- title:
--   Selected-floor prefix certificate for prepared pair 24, left list, part 0
-- statement:
--   For prepared pair 24, left list, part 0, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 101 through 124, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft24_001Part00.lean, lines 11-16, SHA-256 27bc52fc12daf4ca5fa59f35eb0d1fb893da5f82d98b4425feb695111b12b018. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.left_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.leftCached.drop 101)
      (PairLightPrepared24.leftRows.drop 101) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
