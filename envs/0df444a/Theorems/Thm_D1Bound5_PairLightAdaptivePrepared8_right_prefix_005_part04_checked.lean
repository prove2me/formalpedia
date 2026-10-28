-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_005_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_005_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:08.304562+00:00
-- url     : https://prove2.me/theorems/26c8d98f-9eb9-4f53-8154-1eca907ae86b
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list, part 4
-- statement:
--   For prepared pair 8, right list, part 4, the selected-floor certificate succeeds for at most `27` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 464 through 490, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_005Part04.lean, lines 11-16, SHA-256 0533f499c9c304eab2cc688f408ea1e42c4931fb2578c1a58ee8da2225ea3ce0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_005_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 27
      (PairLightPrepared8.rightCached.drop 464)
      (PairLightPrepared8.rightRows.drop 464) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
