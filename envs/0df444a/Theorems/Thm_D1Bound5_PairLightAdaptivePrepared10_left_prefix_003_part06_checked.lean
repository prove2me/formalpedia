-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_003_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_003_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:14.990183+00:00
-- url     : https://prove2.me/theorems/e2fcc9c0-154a-49b9-8a1a-347153397210
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list, part 6
-- statement:
--   For prepared pair 10, left list, part 6, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 402 through 404, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_003Part06.lean, lines 11-16, SHA-256 e122c2b1fd088af3c3a868125836b00d67978e9240e1f66cf36c5b15ff9c7b26. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_003_part06_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 3
      (PairLightPrepared10.leftCached.drop 402)
      (PairLightPrepared10.leftRows.drop 402) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
