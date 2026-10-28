-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.right_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:45.360745+00:00
-- url     : https://prove2.me/theorems/503f191c-0095-4bcd-9ec0-9ef9152a4597
-- title:
--   Selected-floor prefix certificate for prepared pair 10, right list, part 4
-- statement:
--   For prepared pair 10, right list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 46 through 57, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight10_000Part04.lean, lines 11-16, SHA-256 86ef8004bb5ec67bc131f68d21c308ac819e3c99aa0c56a6bf8b8f766579abd3. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.right_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 12
      (PairLightPrepared10.rightCached.drop 46)
      (PairLightPrepared10.rightRows.drop 46) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
