-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_003_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_003_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:12.216977+00:00
-- url     : https://prove2.me/theorems/7bfd6241-22b8-401d-9da7-c0e4b0fdc746
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 2
-- statement:
--   For prepared pair 4, left list, part 2, the selected-floor certificate succeeds for at most `23` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 296 through 318, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_003Part02.lean, lines 11-16, SHA-256 1006233421437905368626a54cff7f0a8788e908ca97e4f4a3b5f01fddaa58f7. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_003_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 23
      (PairLightPrepared4.leftCached.drop 296)
      (PairLightPrepared4.leftRows.drop 296) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
