-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_left_prefix_001_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.left_prefix_001_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:54.288344+00:00
-- url     : https://prove2.me/theorems/11bd9a08-ca7b-42ad-bd66-25ffb6d0c2e4
-- title:
--   Selected-floor prefix certificate for prepared pair 24, left list, part 4
-- statement:
--   For prepared pair 24, left list, part 4, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 197 through 220, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft24_001Part04.lean, lines 11-16, SHA-256 8c8881f2559b5b11cf7657638885ba4c60d3d6a21865ab88ac50c8576b5daefb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.left_prefix_001_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.leftCached.drop 197)
      (PairLightPrepared24.leftRows.drop 197) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
