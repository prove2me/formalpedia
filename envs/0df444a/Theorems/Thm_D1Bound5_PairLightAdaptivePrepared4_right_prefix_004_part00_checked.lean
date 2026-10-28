-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_004_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_004_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:35.031822+00:00
-- url     : https://prove2.me/theorems/e53a0c64-1b55-4ace-87ab-61ba6e043e6f
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list, part 0
-- statement:
--   For prepared pair 4, right list, part 0, the selected-floor certificate succeeds for at most `36` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 405 through 440, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_004Part00.lean, lines 11-16, SHA-256 ecb89b247a6de53ed6bd55c0c29fedaf38294854fe395ca93cb6ceb93c35ab2f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_004_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 36
      (PairLightPrepared4.rightCached.drop 405)
      (PairLightPrepared4.rightRows.drop 405) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
