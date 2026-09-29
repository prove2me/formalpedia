-- Prove2me | Theorems.Thm_BraidsLinksMCG_adjacent_standard_projected_homotopy_child_v2
-- name    : BraidsLinksMCG.adjacent_standard_projected_homotopy_child_v2
-- status  : Open
-- author  : @WillR
-- created : 2026-09-24T06:48:40.391572+00:00
-- url     : https://prove2.me/theorems/f50c303e-14b9-43aa-8279-6c144fd19f80
-- title:
--   The adjacent projected standard loop has the squared-final-half-twist class
-- statement:
--   The projected adjacent standard loop and the concatenation of two final half-twist loops represent the same path-homotopy class.
-- source:
--   Canonical quotient-level form of the adjacent geometric obligation in target a5d61856-8526-4cf8-960c-b185fcf7fd81. This theorem-only interface avoids the mapped-path elaboration boundary exposed by the v1 publication attempt and leaves the homotopy construction in the proof body.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist

open BraidsLinksMCG TarchaBraids

namespace BraidsLinksMCG

theorem adjacent_standard_projected_homotopy_child_v2 (n : ℕ) :
    (let p : Path (baseUnordered (n + 2)) (baseUnordered (n + 2)) :=
      (((standardLoop (n + 1) (Fin.last n)).map
          (configIncl (n + 1)).continuous).cast
        (configIncl_base (n + 1)).symm
        (configIncl_base (n + 1)).symm).map
          (configProj (n + 2)).continuous;
     Path.Homotopic.Quotient.mk p =
       Path.Homotopic.Quotient.mk
         ((halfTwistLoop (n + 2) (Fin.last n)).trans
           (halfTwistLoop (n + 2) (Fin.last n)))) := by sorry

end BraidsLinksMCG
