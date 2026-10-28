-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_000_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.right_prefix_000_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:22.190293+00:00
-- url     : https://prove2.me/theorems/3d34e8b8-6d8f-456d-b7f8-a6cda19a360e
-- title:
--   Selected-floor prefix certificate for prepared pair 7, right list
-- statement:
--   For prepared pair 7, right list, the selected-floor certificate succeeds for at most `106` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`.
-- source:
--   D1Bound5/SmallPairLightRight7Prefix000.lean, lines 16-69, SHA-256 721e6c3de2053f806d5b228acec0be3d008da7db866ffe75da1b8de14c0bf871. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared7.right_prefix_000_direct_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 106
      (PairLightPrepared7.rightCached.drop 0) (PairLightPrepared7.rightRows.drop 0) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared7
end
