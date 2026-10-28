-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared40_right_independent_checked
-- name    : D1Bound5.PairLightPrepared40.right_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:30:19.153301+00:00
-- url     : https://prove2.me/theorems/69059335-24d4-4833-abf9-e1bfd3c794c4
-- title:
--   Pair Light Prepared40 — right independent checked
-- statement:
--   Auxiliary result `PairLightPrepared40.right_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight40.lean, lines 18-33, SHA-256 06543f3086bd72b3c96c84aecdcd618d785dcb2411b070a4a3b29ac447395732. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_005

section
namespace D1Bound5.PairLightPrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared40.right_independent_checked :
    pairLightSelectedFloorIndependentBool 1 2 sieve rightCached rightRows = true := by sorry



end D1Bound5.PairLightPrepared40
end
