-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_002_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_002_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:44.548825+00:00
-- url     : https://prove2.me/theorems/2754db26-a918-4e14-af23-399f5af15b05
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list, part 1
-- statement:
--   For prepared pair 10, left list, part 1, the selected-floor certificate succeeds for at most `16` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 168 through 183, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_002Part01.lean, lines 11-16, SHA-256 5bd6348425d590ddd11e7991e9adee0301e02a56987a1fdd96df968709b5e6f7. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_002_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 16
      (PairLightPrepared10.leftCached.drop 168)
      (PairLightPrepared10.leftRows.drop 168) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
