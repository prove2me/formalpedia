-- Prove2me | Theorems.Thm_BraidsLinksMCG_adjacent_pairConfig_configIncl_coords_child_v1
-- name    : BraidsLinksMCG.adjacent_pairConfig_configIncl_coords_child_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T18:42:21.841067+00:00
-- url     : https://prove2.me/theorems/d7278cd1-a78c-43ed-a285-5b87b297dabf
-- title:
--   The adjacent pair has the coordinates of the standard inclusion
-- statement:
--   The ordered configuration formed by the first n fixed punctures, the next fixed puncture n+1, and a moving point z has exactly the coordinate vector obtained by including z into a plane with n+1 punctures.
-- source:
--   Finite-index endpoint sub-obligation in adjacentPairHomotopyConfig_zero for open leaf a5d61856-8526-4cf8-960c-b185fcf7fd81, candidate 2479. It isolates the exact double-Fin.snoc versus configIncl coordinate rearrangement; the parent supplies the left coordinate n+1 and the moving profile point as its final two coordinates.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
namespace BraidsLinksMCG
theorem adjacent_pairConfig_configIncl_coords_child_v1 (n : ℕ)
    (z : PuncturedPlane (n + 1)) :
    (configIncl (n + 1) z).1 =
      Fin.snoc (Fin.snoc (fun k : Fin n => ((k : ℕ) + 1 : ℂ))
        (((n : ℝ) + 1 : ℝ) : ℂ)) z.1 := by sorry
end BraidsLinksMCG
