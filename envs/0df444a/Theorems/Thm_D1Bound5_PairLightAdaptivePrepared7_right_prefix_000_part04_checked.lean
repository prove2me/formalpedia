-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.right_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:18:48.732824+00:00
-- url     : https://prove2.me/theorems/64c1550e-3bfe-4695-8061-cea1266f2ff0
-- title:
--   Selected-floor prefix certificate for prepared pair 7, right list, part 4
-- statement:
--   For prepared pair 7, right list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 48 through 59, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight7_000Part04.lean, lines 11-16, SHA-256 5dda4b9acdca10f45bf9457ad8a7730eaf6a9c7bff4e72d5d0510a76cfc94243. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.right_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 12
      (PairLightPrepared7.rightCached.drop 48)
      (PairLightPrepared7.rightRows.drop 48) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
