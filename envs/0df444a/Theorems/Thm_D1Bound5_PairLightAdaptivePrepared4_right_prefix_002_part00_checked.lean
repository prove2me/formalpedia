-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:20.437264+00:00
-- url     : https://prove2.me/theorems/7f9c0017-9f87-4dc5-bd1d-6e846963a454
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list, part 0
-- statement:
--   For prepared pair 4, right list, part 0, the selected-floor certificate succeeds for at most `15` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 153 through 167, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_002Part00.lean, lines 11-16, SHA-256 72d5027a4366f55cb27549316ec43420b948b20d4fa4bfed6151b8cbbeea27e7. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_002_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 15
      (PairLightPrepared4.rightCached.drop 153)
      (PairLightPrepared4.rightRows.drop 153) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
