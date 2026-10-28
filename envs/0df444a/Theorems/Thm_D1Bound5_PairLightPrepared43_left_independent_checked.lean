-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared43_left_independent_checked
-- name    : D1Bound5.PairLightPrepared43.left_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:02:49.292554+00:00
-- url     : https://prove2.me/theorems/7fc26ed1-f0ca-4627-8bb7-38269ec015ed
-- title:
--   Pair Light Prepared43 — left independent checked
-- statement:
--   Auxiliary result `PairLightPrepared43.left_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft43.lean, lines 19-39, SHA-256 b4a47defd44bf5d1e37b6de966b05ddd88610a6691a509d4e24545811769fc00. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_003

section
namespace D1Bound5.PairLightPrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared43.left_independent_checked :
    pairLightSelectedFloorIndependentBool 1 3 sieve leftCached leftRows = true := by sorry



end D1Bound5.PairLightPrepared43
end
