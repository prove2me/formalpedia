-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_003_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.right_prefix_003_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:29:04.704336+00:00
-- url     : https://prove2.me/theorems/f4aee015-120f-4a90-8135-e92203ebed89
-- title:
--   Selected-floor prefix certificate for prepared pair 10, right list, part 4
-- statement:
--   For prepared pair 10, right list, part 4, the selected-floor certificate succeeds for at most `27` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 344 through 370, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight10_003Part04.lean, lines 11-16, SHA-256 aaf92cb05b2c93f190c0a872e56ea36c121bf959db806470c8ba63503257e230. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.right_prefix_003_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 27
      (PairLightPrepared10.rightCached.drop 344)
      (PairLightPrepared10.rightRows.drop 344) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
