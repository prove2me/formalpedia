-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_pilot12_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.right_pilot12_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:30:07.440966+00:00
-- url     : https://prove2.me/theorems/4257f4e8-8540-431d-8cd0-e781a7cc6ee9
-- title:
--   Selected-floor prefix certificate for prepared pair 19, right list, part 0
-- statement:
--   For prepared pair 19, right list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 0 through 11, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight19_Pilot12Part00.lean, lines 11-16, SHA-256 afcac624268c819f8c70f2a0a1dc1d9e94d0c4a2720d75110617cfd3b78ddbc1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.right_pilot12_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 12
      (PairLightPrepared19.rightCached.drop 0)
      (PairLightPrepared19.rightRows.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
