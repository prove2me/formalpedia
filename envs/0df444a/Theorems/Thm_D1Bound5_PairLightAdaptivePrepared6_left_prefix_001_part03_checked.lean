-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:09.214705+00:00
-- url     : https://prove2.me/theorems/ed91ca65-7fd2-4f2e-bf71-324c63224084
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 3
-- statement:
--   For prepared pair 6, left list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 98 through 109, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_001Part03.lean, lines 11-16, SHA-256 c2a74cfa8bb66cce2e5d572bd15dba780d4cbbd9e69a9ec22c98169b64ab66f7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 12
      (PairLightPrepared6.leftCached.drop 98)
      (PairLightPrepared6.leftRows.drop 98) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
