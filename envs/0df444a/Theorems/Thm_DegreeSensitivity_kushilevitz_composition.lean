-- Prove2me | Theorems.Thm_DegreeSensitivity_kushilevitz_composition
-- name    : DegreeSensitivity.kushilevitz_composition
-- status  : Open
-- author  : @queelius
-- created : 2026-11-07T16:51:30.281407+00:00
-- url     : https://prove2.me/theorems/3e10b8ed-38ca-4f75-9787-4ebacadceccc
-- title:
--   Composed Kushilevitz functions
-- statement:
--   For every $k \ge 0$, some Boolean function on $6^k$ bits has degree exactly $3^k$, value 0 at the origin, and sensitivity $6^k$ at the origin.
-- source:
--   Composition of a fully sensitive base function with itself on disjoint blocks; Nisan and Szegedy (1994) and Hatami, Kulkarni and Pankratov (2011), Example 5.4 ("the Kushilevitz base h and its powering").

import Definitions.Def_BoolFunc
import Definitions.Def_sensitivity
import Definitions.Def_polyDegree

namespace DegreeSensitivity

theorem kushilevitz_composition (k : ℕ) :
    ∃ f : BoolFunc (6 ^ k), polyDegree f = 3 ^ k ∧ f (fun _ => false) = false ∧
      sensitivityAt f (fun _ => false) = 6 ^ k := by sorry

end DegreeSensitivity
