-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_left_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared12.left_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:23.464114+00:00
-- url     : https://prove2.me/theorems/7fb69617-fabd-45c0-b18d-9aa44e81f5bf
-- title:
--   Selected-floor prefix certificate for prepared pair 12, left list, part 0
-- statement:
--   For prepared pair 12, left list, part 0, the selected-floor certificate succeeds for at most `51` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared12.sieve`. Original heads 138 through 188; every head retains its complete original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft12_001Part00.lean, lines 7-11, SHA-256 f76a6077b233d36bf0c1a409641fcbe2762e667af3956176086521c1f7f7bd81. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared12.left_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 51
      (leftCached001.drop 0) (leftRows001.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared12
end
