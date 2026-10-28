-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_right_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared38.right_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:09.774719+00:00
-- url     : https://prove2.me/theorems/18201a76-6644-40fb-a0c9-350b9985be6d
-- title:
--   Selected-floor prefix certificate for prepared pair 38, right list, part 2
-- statement:
--   For prepared pair 38, right list, part 2, the selected-floor certificate succeeds for at most `58` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared38.sieve`. Original heads 82 through 139; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight38_000Part02.lean, lines 7-11, SHA-256 11d3e3151e6f35dff26a7f6d68ede968244c416f6012756c4a1d85de6c50cd0a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData38_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared38.right_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 58
      (rightCached000.drop 82) (rightRows000.drop 82) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared38
end
