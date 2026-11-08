-- Prove2me | Theorems.Thm_DegreeSensitivity_kushilevitz
-- name    : DegreeSensitivity.kushilevitz
-- status  : Open
-- author  : @queelius
-- created : 2026-11-07T16:51:18.762717+00:00
-- url     : https://prove2.me/theorems/17b412d4-4581-467a-be10-550522bf386d
-- title:
--   Kushilevitz's six-variable function
-- statement:
--   Some Boolean function on 6 bits has degree exactly 3, value 0 at the origin, and sensitivity 6 at the origin (it is fully sensitive at $\mathbf 0$).
-- source:
--   E. Kushilevitz, reported in N. Nisan and A. Wigderson, On rank vs. communication complexity, Combinatorica 15 (1995), footnote 1 on p. 560; explicit formula in K. Amano, Bulletin of the EATCS 101 (2010), and in Hatami, Kulkarni and Pankratov, Theory of Computing Graduate Surveys 4 (2011), Example 5.4.

import Definitions.Def_BoolFunc
import Definitions.Def_sensitivity
import Definitions.Def_polyDegree

namespace DegreeSensitivity

theorem kushilevitz :
    ∃ f : BoolFunc 6, polyDegree f = 3 ∧ f (fun _ => false) = false ∧
      sensitivityAt f (fun _ => false) = 6 := by sorry

end DegreeSensitivity
