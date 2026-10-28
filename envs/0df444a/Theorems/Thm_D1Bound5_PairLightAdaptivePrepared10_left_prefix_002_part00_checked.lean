-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:56.468608+00:00
-- url     : https://prove2.me/theorems/b1261bc9-0f49-40f3-ad90-18da4d133184
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list, part 0
-- statement:
--   For prepared pair 10, left list, part 0, the selected-floor certificate succeeds for at most `15` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 153 through 167, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_002Part00.lean, lines 11-16, SHA-256 aa5fed811b312c9ad33cb2d52e22a905ddeb3927bdfaebf536491a40dc58512d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_002_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 15
      (PairLightPrepared10.leftCached.drop 153)
      (PairLightPrepared10.leftRows.drop 153) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
