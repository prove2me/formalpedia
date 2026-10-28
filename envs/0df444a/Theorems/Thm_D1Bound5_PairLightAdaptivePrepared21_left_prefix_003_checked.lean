-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_prefix_003_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_prefix_003_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:25:26.140883+00:00
-- url     : https://prove2.me/theorems/d4888d02-128f-41fe-8de4-b64ab7fe7f4b
-- title:
--   Selected-floor prefix certificate for prepared pair 21, left list
-- statement:
--   For prepared pair 21, left list, the selected-floor certificate succeeds for at most `189` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft21_003.lean, lines 24-119, SHA-256 ffe3f40bb5e722a5270213e1cff005d4a4f7b087397941e59cffa198e808ed7f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData21_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_prefix_003_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 189
      leftCached003 leftRows003 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
