-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_prefix_002_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.right_prefix_002_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:51.510384+00:00
-- url     : https://prove2.me/theorems/f5ad448e-ebc2-43ed-810f-7c089bd3287e
-- title:
--   Selected-floor prefix certificate for prepared pair 24, right list, part 2
-- statement:
--   For prepared pair 24, right list, part 2, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 296 through 319, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight24_002Part02.lean, lines 11-16, SHA-256 591c7dff3fe0f5cea7823ea3e43cab8a3b544fe14b2c4920590d5386e3291747. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.right_prefix_002_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.rightCached.drop 296)
      (PairLightPrepared24.rightRows.drop 296) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
