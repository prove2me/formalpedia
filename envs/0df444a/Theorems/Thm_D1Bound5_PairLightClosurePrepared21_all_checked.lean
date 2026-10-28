-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared21_all_checked
-- name    : D1Bound5.PairLightClosurePrepared21.all_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:37:39.206845+00:00
-- url     : https://prove2.me/theorems/86967e4c-92db-422c-aaa5-2d8dba0581a8
-- title:
--   Pair Light Closure Prepared21 — all checked
-- statement:
--   Auxiliary result `PairLightClosurePrepared21.all_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairPureClosure21.lean, lines 24-115, SHA-256 61459d5bd0d8f75534203a210f44416731d06ea568715d2d347706a8548b614f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21_Definitions

section
namespace D1Bound5.PairLightClosurePrepared21
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightClosurePrepared21.all_checked :
    pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      witnesses destinations = true := by sorry

end D1Bound5.PairLightClosurePrepared21
end
