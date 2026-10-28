-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared11_right_independent_checked
-- name    : D1Bound5.PairLightPrepared11.right_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:06:42.049516+00:00
-- url     : https://prove2.me/theorems/aedc931d-fbeb-4a44-841b-a7b19fd22675
-- title:
--   Pair Light Prepared11 — right independent checked
-- statement:
--   Auxiliary result `PairLightPrepared11.right_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight11.lean, lines 18-33, SHA-256 df0aa3ffd451b6c69d6a0e6fa43c3aa3da6cc1230bb0bc3d8ebde46d49ba607b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData11RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Right_Definitions_002

section
namespace D1Bound5.PairLightPrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared11.right_independent_checked :
    pairLightSelectedFloorIndependentBool 0 1 sieve rightCached rightRows = true := by sorry



end D1Bound5.PairLightPrepared11
end
