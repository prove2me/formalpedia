-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared39_left_independent_checked
-- name    : D1Bound5.PairLightPrepared39.left_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:25:10.156871+00:00
-- url     : https://prove2.me/theorems/4aa77d46-374d-4b3e-b000-a0854b2f01bf
-- title:
--   Pair Light Prepared39 — left independent checked
-- statement:
--   Auxiliary result `PairLightPrepared39.left_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft39.lean, lines 19-39, SHA-256 94ff7c1748ece0224e55c272f00f27c3d6c9d693d05edca7b84a598d77c8b601. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightPrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared39.left_independent_checked :
    pairLightSelectedFloorIndependentBool 1 2 sieve leftCached leftRows = true := by sorry



end D1Bound5.PairLightPrepared39
end
