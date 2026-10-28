-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_prefix_002_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_prefix_002_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:46:37.708221+00:00
-- url     : https://prove2.me/theorems/6a667bd0-4692-44ed-a953-b2c511b33df4
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list
-- statement:
--   For prepared pair 28, left list, the selected-floor certificate succeeds for at most `151` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft28_002.lean, lines 21-98, SHA-256 9e916fa26705e0e8981c80fd0b3bbfbd9ea5b1565112aaf4f5ce94fb0a84f4b6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData28_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 151
      leftCached002 leftRows002 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
