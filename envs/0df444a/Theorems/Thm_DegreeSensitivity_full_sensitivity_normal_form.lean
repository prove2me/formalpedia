-- Prove2me | Theorems.Thm_DegreeSensitivity_full_sensitivity_normal_form
-- name    : DegreeSensitivity.full_sensitivity_normal_form
-- status  : Open
-- author  : @queelius
-- created : 2026-11-07T16:52:10.003139+00:00
-- url     : https://prove2.me/theorems/da4d0abf-d4dd-4843-bf69-4db86d38e448
-- title:
--   Normal form for degree five and sensitivity fourteen
-- statement:
--   Some Boolean function (on any number of bits) has degree at most 5 and sensitivity at least 14 if and only if some Boolean function $g$ on 14 bits has degree at most 5, $g(\mathbf 0) = 0$ and $g(e_i) = 1$ for all $i$.
-- source:
--   Standard normalization (restriction to sensitive coordinates, translation of the sensitive point to the origin, negation), as in Nisan and Szegedy (1994) and the remark in the Epoch statement; derived reduction, not a numbered theorem of a cited paper.

import Definitions.Def_BoolFunc
import Definitions.Def_sensitivity
import Definitions.Def_polyDegree

namespace DegreeSensitivity

theorem full_sensitivity_normal_form :
    (∃ (n : ℕ) (f : BoolFunc n), polyDegree f ≤ 5 ∧ 14 ≤ sensitivity f) ↔
      ∃ g : BoolFunc 14, polyDegree g ≤ 5 ∧ g (fun _ => false) = false ∧
        ∀ i : Fin 14, g (Function.update (fun _ => false) i true) = true := by sorry

end DegreeSensitivity
