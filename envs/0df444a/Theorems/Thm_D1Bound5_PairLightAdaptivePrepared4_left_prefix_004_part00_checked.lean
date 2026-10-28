-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_004_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_004_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:42.504901+00:00
-- url     : https://prove2.me/theorems/13257658-420d-46e7-a519-5a68afd9a001
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 0
-- statement:
--   For prepared pair 4, left list, part 0, the selected-floor certificate succeeds for at most `36` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 405 through 440, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_004Part00.lean, lines 11-16, SHA-256 bc3420f23f31bd368c407f0cb8632f011dac8096a7aeeb3af51a911bc1c6b9df. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_004_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 36
      (PairLightPrepared4.leftCached.drop 405)
      (PairLightPrepared4.leftRows.drop 405) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
