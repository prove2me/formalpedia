-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_003_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_003_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:14.162229+00:00
-- url     : https://prove2.me/theorems/b89f66ca-9904-4d04-92ec-8fd4d1948897
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list, part 1
-- statement:
--   For prepared pair 4, right list, part 1, the selected-floor certificate succeeds for at most `21` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 275 through 295, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_003Part01.lean, lines 11-16, SHA-256 48b32391ca1942cedc4aed1556f30ec08886e83e21ce8229a4ac4ee2c2625a87. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_003_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 21
      (PairLightPrepared4.rightCached.drop 275)
      (PairLightPrepared4.rightRows.drop 275) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
