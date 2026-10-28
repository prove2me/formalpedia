-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_prefix_002_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_prefix_002_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:21.242582+00:00
-- url     : https://prove2.me/theorems/39a904b1-afb7-41cc-a8ff-6581054e7279
-- title:
--   Selected-floor prefix certificate for prepared pair 21, left list
-- statement:
--   For prepared pair 21, left list, the selected-floor certificate succeeds for at most `151` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft21_002.lean, lines 21-98, SHA-256 effeeeaeff79d83ccf53983bdbedc456f834a89056a564110b342894069ede25. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData21_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 151
      leftCached002 leftRows002 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
