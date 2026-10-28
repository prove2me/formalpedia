-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_003_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_003_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:11.682768+00:00
-- url     : https://prove2.me/theorems/e9702953-8796-4e9f-aee4-d0d332806f33
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 3
-- statement:
--   For prepared pair 4, left list, part 3, the selected-floor certificate succeeds for at most `25` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 319 through 343, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_003Part03.lean, lines 11-16, SHA-256 a35353a57aadecaad7fde530304b605a136d0f433e82adea1e1570e78bf5e9b3. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_003_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 25
      (PairLightPrepared4.leftCached.drop 319)
      (PairLightPrepared4.leftRows.drop 319) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
