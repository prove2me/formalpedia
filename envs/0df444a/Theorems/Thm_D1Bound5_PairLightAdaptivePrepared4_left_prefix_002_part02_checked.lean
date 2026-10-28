-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_002_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_002_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:04.589177+00:00
-- url     : https://prove2.me/theorems/6202b400-0316-444e-9985-8f2ceef48dbf
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 2
-- statement:
--   For prepared pair 4, left list, part 2, the selected-floor certificate succeeds for at most `17` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 184 through 200, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_002Part02.lean, lines 11-16, SHA-256 ab05128343e7b418956cea02a2c3a3cd8c1ad76968f80a35f88a4eb1d621b9a8. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_002_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 17
      (PairLightPrepared4.leftCached.drop 184)
      (PairLightPrepared4.leftRows.drop 184) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
