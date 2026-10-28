-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared43_right_independent_checked
-- name    : D1Bound5.PairLightPrepared43.right_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:29:37.228584+00:00
-- url     : https://prove2.me/theorems/302f9f55-b942-42b1-a24f-b4b8cc5d3d59
-- title:
--   Pair Light Prepared43 — right independent checked
-- statement:
--   Auxiliary result `PairLightPrepared43.right_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight43.lean, lines 19-39, SHA-256 778ebaf7087baf2c2c52c6723d8d0407db4d514b6cbf9df3656965adc2fb2674. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_003

section
namespace D1Bound5.PairLightPrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared43.right_independent_checked :
    pairLightSelectedFloorIndependentBool 1 3 sieve rightCached rightRows = true := by sorry



end D1Bound5.PairLightPrepared43
end
