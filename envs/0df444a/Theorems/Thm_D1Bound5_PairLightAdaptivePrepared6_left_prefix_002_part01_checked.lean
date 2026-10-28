-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_002_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_002_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:12.894293+00:00
-- url     : https://prove2.me/theorems/d2847c0d-7e16-431f-86c5-3d50cccba41f
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 1
-- statement:
--   For prepared pair 6, left list, part 1, the selected-floor certificate succeeds for at most `13` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 147 through 159, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_002Part01.lean, lines 11-16, SHA-256 2da65b68c7641f5aebd5f4f852b3ec803aa0a5fc276a39ccf6c6d1c55a05c4ae. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_002_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 13
      (PairLightPrepared6.leftCached.drop 147)
      (PairLightPrepared6.leftRows.drop 147) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
