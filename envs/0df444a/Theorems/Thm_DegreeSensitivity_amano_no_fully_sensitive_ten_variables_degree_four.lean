-- Prove2me | Theorems.Thm_DegreeSensitivity_amano_no_fully_sensitive_ten_variables_degree_four
-- name    : DegreeSensitivity.amano_no_fully_sensitive_ten_variables_degree_four
-- status  : Open
-- author  : @queelius
-- created : 2026-11-07T16:52:00.229312+00:00
-- url     : https://prove2.me/theorems/9a56b537-08f7-438b-9369-0b2c56344fee
-- title:
--   Amano: no fully sensitive degree-4 function on 10 variables
-- statement:
--   No Boolean function on 10 bits has degree at most 4 and sensitivity 10.
-- source:
--   K. Amano, Researching the complexity of Boolean functions with computers, Bulletin of the EATCS 101 (2010), 64-91, Theorem 3: "There are no Boolean functions f on 10 variables such that f is fully sensitive and the degree of f is at most 4."

import Definitions.Def_BoolFunc
import Definitions.Def_sensitivity
import Definitions.Def_polyDegree

namespace DegreeSensitivity

theorem amano_no_fully_sensitive_ten_variables_degree_four :
    ¬ ∃ f : BoolFunc 10, polyDegree f ≤ 4 ∧ sensitivity f = 10 := by sorry

end DegreeSensitivity
