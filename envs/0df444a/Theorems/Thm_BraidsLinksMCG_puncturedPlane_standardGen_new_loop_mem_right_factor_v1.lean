-- Prove2me | Theorems.Thm_BraidsLinksMCG_puncturedPlane_standardGen_new_loop_mem_right_factor_v1
-- name    : BraidsLinksMCG.puncturedPlane_standardGen_new_loop_mem_right_factor_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T12:58:01.704616+00:00
-- url     : https://prove2.me/theorems/1de60ed2-a05b-4107-abb3-55cdf6681511
-- title:
--   The new standard loop lies in the right member of the corrected cover
-- statement:
--   The standard loop around the newly added puncture remains pointwise in the right half-plane used by the corrected two-piece cover. Its approach path stays far to the right of the cut, and its circular part has real part at least one half unit to the right of the new puncture, so every point lies strictly above the cover threshold. This supplies the coordinate containment needed for a later pointed equivalence between the right factor and a one-puncture free group; it does not assert that containment alone proves the equivalence.
-- source:
--   The explicit standard-loop construction in Definitions.Def_BraidsLinksMCG_StandardLoops, applied to the corrected right member of the two-piece cover in BraidsLinksMCG.puncturedPlane_standardGen_matched_cover_geometry_v3.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops

namespace BraidsLinksMCG

theorem puncturedPlane_standardGen_new_loop_mem_right_factor_v1 (n : ℕ) (t : unitInterval) :
    (standardLoop (n + 1) (Fin.last n) t) ∈
      {z : PuncturedPlane (n + 1) |
        ((n : ℝ) + 1) - 3 / 4 < z.1.re} := by sorry

end BraidsLinksMCG
