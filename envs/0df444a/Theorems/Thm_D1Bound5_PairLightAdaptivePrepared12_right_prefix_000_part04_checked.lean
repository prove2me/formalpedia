-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_right_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared12.right_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:10.605996+00:00
-- url     : https://prove2.me/theorems/28a251ed-2307-468c-8b19-b9b404957081
-- title:
--   Selected-floor prefix certificate for prepared pair 12, right list, part 4
-- statement:
--   For prepared pair 12, right list, part 4, the selected-floor certificate succeeds for at most `2` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared12.sieve`. Original heads 136 through 137; every head retains its complete original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight12_000Part04.lean, lines 7-11, SHA-256 736f5724350e46870f4093e7141f6a3e1bfd26382761b46a7c78b1a88394365e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared12.right_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 2
      (rightCached000.drop 136) (rightRows000.drop 136) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared12
end
