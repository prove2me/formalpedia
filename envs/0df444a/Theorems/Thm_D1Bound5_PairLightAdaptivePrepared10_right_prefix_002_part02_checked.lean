-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_002_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.right_prefix_002_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:02:11.237665+00:00
-- url     : https://prove2.me/theorems/4bf7a5bf-fb50-4a6f-9357-5f08da71e673
-- title:
--   Selected-floor prefix certificate for prepared pair 10, right list, part 2
-- statement:
--   For prepared pair 10, right list, part 2, the selected-floor certificate succeeds for at most `17` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 184 through 200, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight10_002Part02.lean, lines 11-16, SHA-256 5fe8a34436fd298d173def9bc814b3e6e2093683f7ca9b3c77bc4232fa2bbf9e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.right_prefix_002_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 17
      (PairLightPrepared10.rightCached.drop 184)
      (PairLightPrepared10.rightRows.drop 184) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
