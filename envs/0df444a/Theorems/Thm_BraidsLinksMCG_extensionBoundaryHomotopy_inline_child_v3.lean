-- Prove2me | Theorems.Thm_BraidsLinksMCG_extensionBoundaryHomotopy_inline_child_v3
-- name    : BraidsLinksMCG.extensionBoundaryHomotopy_inline_child_v3
-- status  : Open
-- author  : @WillR
-- created : 2026-09-23T19:49:27.343206+00:00
-- url     : https://prove2.me/theorems/0966d707-0b5a-44bd-a6af-e9baacd870ee
-- title:
--   Inline strand-extension boundary paths are homotopic (qualified interface)
-- statement:
--   The projected included standard loop followed by the final half-twist is homotopic relative to endpoints to the final half-twist followed by the addU image of the original loop.
-- source:
--   Fresh theorem-only replacement for v2: fully qualifies configIncl_base after canonical raw-target lint rejected the unqualified identifier.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_strand_extension_v1
open BraidsLinksMCG TarchaBraids TarchaBraids.StrandExtension

theorem BraidsLinksMCG.extensionBoundaryHomotopy_inline_child_v3 (n : ℕ) (j : Fin n) :
    (((((standardLoop (n + 1) j.castSucc).map
          (configIncl (n + 1)).continuous).cast
        (BraidsLinksMCG.configIncl_base (n + 1)).symm (BraidsLinksMCG.configIncl_base (n + 1)).symm).map
        (configProj (n + 2)).continuous).trans
      (halfTwistLoop (n + 2) (Fin.last n))).Homotopic
      ((halfTwistLoop (n + 2) (Fin.last n)).trans
        ((((((standardLoop n j).map (configIncl n).continuous).cast
          (BraidsLinksMCG.configIncl_base n).symm (BraidsLinksMCG.configIncl_base n).symm).map
            (configProj (n + 1)).continuous).map
          (TarchaBraids.StrandExtension.addU (n + 1)).continuous).cast
          (TarchaBraids.StrandExtension.addU_base (n + 1)).symm
          (TarchaBraids.StrandExtension.addU_base (n + 1)).symm)) := by sorry
