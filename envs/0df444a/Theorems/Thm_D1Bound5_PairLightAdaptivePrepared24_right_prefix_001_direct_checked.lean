-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_prefix_001_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.right_prefix_001_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:41.399439+00:00
-- url     : https://prove2.me/theorems/65a03cf6-49ce-4d84-98d9-b1991a3d5ed6
-- title:
--   Selected-floor prefix certificate for prepared pair 24, right list
-- statement:
--   For prepared pair 24, right list, the selected-floor certificate succeeds for at most `147` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`.
-- source:
--   D1Bound5/SmallPairLightRight24Prefix001.lean, lines 14-55, SHA-256 6d419c01bfde56966ea1cee9c1815c8e74df641de7b15870e0e4a539b9f3e999. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared24.right_prefix_001_direct_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 147
      (PairLightPrepared24.rightCached.drop 101) (PairLightPrepared24.rightRows.drop 101) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared24
end
