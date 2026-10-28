-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:17.157063+00:00
-- url     : https://prove2.me/theorems/a9702efe-60d7-455e-9eb2-1237c63f26ab
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list
-- statement:
--   For prepared pair 36, right list, the selected-floor certificate succeeds for at most `91` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight36_001.lean, lines 16-63, SHA-256 af2cf7122f08c64aa126f74b913867058ec18ef1edec08643fd0bda9e9613f69. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData36_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 91
      rightCached001 rightRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
