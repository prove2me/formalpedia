-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_002_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_002_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:51:21.652983+00:00
-- url     : https://prove2.me/theorems/c350063f-aca2-423a-b8ec-16bf319c3f56
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list, part 4
-- statement:
--   For prepared pair 4, right list, part 4, the selected-floor certificate succeeds for at most `18` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 218 through 235, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_002Part04.lean, lines 11-16, SHA-256 3e7f3d171cc94039c41ad11d5500e081db2dd21cb833a2b3a611437ec01d4067. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_002_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 18
      (PairLightPrepared4.rightCached.drop 218)
      (PairLightPrepared4.rightRows.drop 218) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
