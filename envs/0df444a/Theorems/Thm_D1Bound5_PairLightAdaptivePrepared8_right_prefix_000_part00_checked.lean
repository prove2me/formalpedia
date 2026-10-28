-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:56.932193+00:00
-- url     : https://prove2.me/theorems/796e040f-a913-44d5-95af-b513bc5b4568
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list, part 0
-- statement:
--   For prepared pair 8, right list, part 0, the selected-floor certificate succeeds for at most `9` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 0 through 8, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_000Part00.lean, lines 11-16, SHA-256 17ae97150543b4a8664315c419b56aa366ae024a3a95fbf2f4b520935558af7e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 9
      (PairLightPrepared8.rightCached.drop 0)
      (PairLightPrepared8.rightRows.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
