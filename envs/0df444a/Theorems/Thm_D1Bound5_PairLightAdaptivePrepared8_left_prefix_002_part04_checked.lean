-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_002_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_002_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:19.718876+00:00
-- url     : https://prove2.me/theorems/5c457f59-60cd-4900-a559-bf40f262157a
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 4
-- statement:
--   For prepared pair 8, left list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 168 through 179, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_002Part04.lean, lines 11-16, SHA-256 461f969e274146a1c6e0b6f8efcb12c03f17f9ea8b8a1d120bbf70849a5741d4. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_002_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 12
      (PairLightPrepared8.leftCached.drop 168)
      (PairLightPrepared8.leftRows.drop 168) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
