-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared14_left_independent_checked
-- name    : D1Bound5.PairLightPrepared14.left_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:33:55.718985+00:00
-- url     : https://prove2.me/theorems/b3e6d1a5-8dc7-4954-8a50-b06c0fdfd1ad
-- title:
--   Pair Light Prepared14 — left independent checked
-- statement:
--   Auxiliary result `PairLightPrepared14.left_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft14.lean, lines 20-45, SHA-256 10628cf5e42f18767c1415f9a8f0aad0342124c383f9d9d555127ce130b5992e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightPrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared14.left_independent_checked :
    pairLightSelectedFloorIndependentBool 0 2 sieve leftCached leftRows = true := by sorry



end D1Bound5.PairLightPrepared14
end
