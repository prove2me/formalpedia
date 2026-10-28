-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_004_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_004_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:05.88423+00:00
-- url     : https://prove2.me/theorems/f95864f0-0ecb-4ff1-94ce-40dbb12b433d
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 0
-- statement:
--   For prepared pair 6, right list, part 0, the selected-floor certificate succeeds for at most `20` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 321 through 340, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_004Part00.lean, lines 11-16, SHA-256 501b2690c9d2c74b262d29799ba294882562e9fcc7dab562df2acc177c40d386. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_004_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 20
      (PairLightPrepared6.rightCached.drop 321)
      (PairLightPrepared6.rightRows.drop 321) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
