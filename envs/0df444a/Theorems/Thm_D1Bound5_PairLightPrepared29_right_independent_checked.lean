-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared29_right_independent_checked
-- name    : D1Bound5.PairLightPrepared29.right_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:13:40.26437+00:00
-- url     : https://prove2.me/theorems/7ffeba33-05ba-46c6-a7ab-42bd1bc548cb
-- title:
--   Pair Light Prepared29 — right independent checked
-- statement:
--   Auxiliary result `PairLightPrepared29.right_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight29.lean, lines 18-33, SHA-256 80c7ed9a3fdaf1f16f1f6fbad169c6a434e215d92c6e4aeb615d65eb3d227578. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData29Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData29Right_Definitions_003

section
namespace D1Bound5.PairLightPrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared29.right_independent_checked :
    pairLightSelectedFloorIndependentBool 1 1 sieve rightCached rightRows = true := by sorry



end D1Bound5.PairLightPrepared29
end
