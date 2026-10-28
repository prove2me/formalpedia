-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_right_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared12.right_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:37.727455+00:00
-- url     : https://prove2.me/theorems/d633a5b7-76dc-4356-b4d4-58e087c77b7e
-- title:
--   Selected-floor prefix certificate for prepared pair 12, right list, part 2
-- statement:
--   For prepared pair 12, right list, part 2, the selected-floor certificate succeeds for at most `35` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared12.sieve`. Original heads 60 through 94; every head retains its complete original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight12_000Part02.lean, lines 7-11, SHA-256 ad12003dca4b9ed698d309b80baccf5bb551e7f7e3990f502212cce5580b73be. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared12.right_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 35
      (rightCached000.drop 60) (rightRows000.drop 60) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared12
end
