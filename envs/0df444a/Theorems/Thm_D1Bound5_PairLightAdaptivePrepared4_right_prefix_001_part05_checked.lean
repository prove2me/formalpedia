-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:56.76098+00:00
-- url     : https://prove2.me/theorems/e0fa1cea-6dc3-4228-887a-91a4c3d956f8
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list, part 5
-- statement:
--   For prepared pair 4, right list, part 5, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 139 through 152, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_001Part05.lean, lines 11-16, SHA-256 16b15329dd16383c2b0fbfba7f5d1be3e47ba2acb8c6dd522ffe8e9d679c8dad. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_001_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 14
      (PairLightPrepared4.rightCached.drop 139)
      (PairLightPrepared4.rightRows.drop 139) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
