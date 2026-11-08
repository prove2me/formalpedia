-- Prove2me | Theorems.Thm_DegreeSensitivity_tal_blockSensitivity_le_polyDegree_sq
-- name    : DegreeSensitivity.tal_blockSensitivity_le_polyDegree_sq
-- status  : Open
-- author  : @queelius
-- created : 2026-11-07T16:51:40.388206+00:00
-- url     : https://prove2.me/theorems/d7304857-2fe4-4500-84f8-a9ddc8d255c4
-- title:
--   Tal's bound: block sensitivity at most degree squared
-- statement:
--   For every Boolean function $f$, $bs(f) \le \deg(f)^2$.
-- source:
--   A. Tal, Properties and applications of Boolean function composition, ITCS 2013, 441-454, doi:10.1145/2422436.2422485 (improving Nisan and Szegedy 1994 by a factor 2).

import Definitions.Def_BoolFunc
import Definitions.Def_blockSensitivity
import Definitions.Def_polyDegree

namespace DegreeSensitivity

theorem tal_blockSensitivity_le_polyDegree_sq {n : ℕ} (f : BoolFunc n) :
    blockSensitivity f ≤ polyDegree f ^ 2 := by sorry

end DegreeSensitivity
