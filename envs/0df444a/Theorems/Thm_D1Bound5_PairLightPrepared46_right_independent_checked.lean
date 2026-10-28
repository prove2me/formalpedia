-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared46_right_independent_checked
-- name    : D1Bound5.PairLightPrepared46.right_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:46:39.898999+00:00
-- url     : https://prove2.me/theorems/e466fa6f-7001-4ec9-9ee9-6871e20fb57a
-- title:
--   Pair Light Prepared46 — right independent checked
-- statement:
--   Auxiliary result `PairLightPrepared46.right_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight46.lean, lines 18-33, SHA-256 739c702ff1f9840879a27681847c112e22b302f45be3cd1ea64e1144781104cd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData46RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Right_Definitions_002

section
namespace D1Bound5.PairLightPrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared46.right_independent_checked :
    pairLightSelectedFloorIndependentBool 1 6 sieve rightCached rightRows = true := by sorry



end D1Bound5.PairLightPrepared46
end
