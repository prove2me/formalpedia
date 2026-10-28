-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared36_left_independent_checked
-- name    : D1Bound5.PairLightPrepared36.left_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:24:24.673992+00:00
-- url     : https://prove2.me/theorems/ffe63a88-5b74-422c-ba06-fa21b185e5d6
-- title:
--   Pair Light Prepared36 — left independent checked
-- statement:
--   Auxiliary result `PairLightPrepared36.left_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft36.lean, lines 20-45, SHA-256 fcc74b2ada6ab2c30b6f237bc30ff4fab95ab80fe33464a3c6b0e713456aea31. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightPrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared36.left_independent_checked :
    pairLightSelectedFloorIndependentBool 1 2 sieve leftCached leftRows = true := by sorry



end D1Bound5.PairLightPrepared36
end
