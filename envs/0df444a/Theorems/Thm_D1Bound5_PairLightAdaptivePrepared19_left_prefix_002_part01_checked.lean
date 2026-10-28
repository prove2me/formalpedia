-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_left_prefix_002_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.left_prefix_002_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:52.093816+00:00
-- url     : https://prove2.me/theorems/a5ea6d1d-e3ac-4d22-af73-5c64f87dae4c
-- title:
--   Selected-floor prefix certificate for prepared pair 19, left list, part 1
-- statement:
--   For prepared pair 19, left list, part 1, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 272 through 295, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft19_002Part01.lean, lines 11-16, SHA-256 8ce66f29608940d1eb4bff33842c1102f28f6df07c0bf0f74517334f405e1ce4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.left_prefix_002_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.leftCached.drop 272)
      (PairLightPrepared19.leftRows.drop 272) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
