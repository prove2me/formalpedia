-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared30_all_checked
-- name    : D1Bound5.PairLightClosurePrepared30.all_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:34:21.973577+00:00
-- url     : https://prove2.me/theorems/7edc10d6-6de4-4798-af8a-a5da57bea1b8
-- title:
--   Pair Light Closure Prepared30 — all checked
-- statement:
--   Auxiliary result `PairLightClosurePrepared30.all_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairPureClosure30.lean, lines 23-109, SHA-256 8cb62247448a15102bc10cd308ae79653e4a63a59334c1d71c4da0ca4bd761a0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30_Definitions

section
namespace D1Bound5.PairLightClosurePrepared30
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightClosurePrepared30.all_checked :
    pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      witnesses destinations = true := by sorry

end D1Bound5.PairLightClosurePrepared30
end
