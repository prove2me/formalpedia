-- Prove2me | Theorems.Thm_BraidsLinksMCG_extensionBoundaryHomotopy_inline_child_v1
-- name    : BraidsLinksMCG.extensionBoundaryHomotopy_inline_child_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-23T19:39:33.153646+00:00
-- url     : https://prove2.me/theorems/f53f3cae-14e0-416d-a809-4c0269acd36e
-- title:
--   The strand-extension boundary homotopy with inline paths
-- statement:
--   The projected image of the standard loop on the added configuration, followed by the final half-twist, is homotopic relative to endpoints to the final half-twist followed by the added image of the original loop.
-- source:
--   The theorem-only replacement for the boundary-homotopy subgoal of open target 2273a291-a4e8-43a8-b38b-527095999a64. It states the exact two boundary path concatenations directly, avoiding auxiliary declarations in the target interface.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_strand_extension_v1

open BraidsLinksMCG TarchaBraids TarchaBraids.StrandExtension

namespace BraidsLinksMCG

theorem extensionBoundaryHomotopy_inline_child_v1 (n : ℕ) (j : Fin n) :
    (((((standardLoop (n + 1) j.castSucc).map
          (configIncl (n + 1)).continuous).cast
        (configIncl_base (n + 1)).symm (configIncl_base (n + 1)).symm).map
        (configProj (n + 2)).continuous).trans
      (halfTwistLoop (n + 2) (Fin.last n))).Homotopic
      ((halfTwistLoop (n + 2) (Fin.last n)).trans
        ((((((standardLoop n j).map (configIncl n).continuous).cast
          (configIncl_base n).symm (configIncl_base n).symm).map
            (configProj (n + 1)).continuous).map (addU (n + 1)).continuous).cast
          (addU_base (n + 1)).symm (addU_base (n + 1)).symm)) := by sorry
end BraidsLinksMCG
