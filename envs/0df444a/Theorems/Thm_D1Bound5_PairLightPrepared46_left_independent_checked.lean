-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared46_left_independent_checked
-- name    : D1Bound5.PairLightPrepared46.left_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:36:56.297606+00:00
-- url     : https://prove2.me/theorems/c5f639a5-406f-48ca-a298-e2da910ef543
-- title:
--   Pair Light Prepared46 — left independent checked
-- statement:
--   Auxiliary result `PairLightPrepared46.left_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft46.lean, lines 18-33, SHA-256 1f83b52da398d7859b2344f560660efce4764f16abde756d5407b114342d3f4f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_002

section
namespace D1Bound5.PairLightPrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared46.left_independent_checked :
    pairLightSelectedFloorIndependentBool 1 6 sieve leftCached leftRows = true := by sorry



end D1Bound5.PairLightPrepared46
end
