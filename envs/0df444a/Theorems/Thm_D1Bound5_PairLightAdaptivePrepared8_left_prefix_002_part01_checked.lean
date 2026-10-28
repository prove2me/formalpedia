-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_002_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_002_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:27.681033+00:00
-- url     : https://prove2.me/theorems/bc25443a-5b4e-47d6-8b9a-058d927ba1bb
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 1
-- statement:
--   For prepared pair 8, left list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 132 through 143, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_002Part01.lean, lines 11-16, SHA-256 6066a976374beec491f0ef7f5b51552325561a1c1bb3b8315c33882f2f453612. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_002_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 12
      (PairLightPrepared8.leftCached.drop 132)
      (PairLightPrepared8.leftRows.drop 132) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
