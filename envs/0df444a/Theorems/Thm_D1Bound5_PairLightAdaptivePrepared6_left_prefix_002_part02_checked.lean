-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_002_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_002_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:04.427981+00:00
-- url     : https://prove2.me/theorems/684ecc49-7dfa-4774-bc68-a9618bad1bca
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 2
-- statement:
--   For prepared pair 6, left list, part 2, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 160 through 173, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_002Part02.lean, lines 11-16, SHA-256 ca53cd85cad2a25b7e287ca678342ae77b110bd04750a4404107fd3e927c6628. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_002_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 14
      (PairLightPrepared6.leftCached.drop 160)
      (PairLightPrepared6.leftRows.drop 160) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
