-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.right_parallel_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:09.832496+00:00
-- url     : https://prove2.me/theorems/3982ed1b-1002-485f-9fd1-16cb92df85aa
-- title:
--   Selected-floor prefix certificate for prepared pair 30, right list, part 1
-- statement:
--   For prepared pair 30, right list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 12 through 23, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight30_000Part01.lean, lines 10-14, SHA-256 4718ff0ab8deb067655726a5e976458f296a5fa927b3406a953fc33091bee57d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.right_parallel_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 12) (PairLightPrepared30.rightRows.drop 12) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
