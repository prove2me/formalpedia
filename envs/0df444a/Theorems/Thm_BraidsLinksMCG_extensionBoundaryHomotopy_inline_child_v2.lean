-- Prove2me | Theorems.Thm_BraidsLinksMCG_extensionBoundaryHomotopy_inline_child_v2
-- name    : BraidsLinksMCG.extensionBoundaryHomotopy_inline_child_v2
-- status  : Open
-- author  : @WillR
-- created : 2026-09-23T19:46:45.263985+00:00
-- url     : https://prove2.me/theorems/0a7b8812-04c2-4021-9593-bcff7b5df5d6
-- title:
--   Inline strand-extension boundary paths are homotopic
-- statement:
--   The projected included standard loop followed by the final half-twist is homotopic relative to endpoints to the final half-twist followed by the addU image of the original loop.
-- source:
--   Corrected theorem-only child replacing unsupported auxiliary declarations in target f53f3cae-14e0-416d-a809-4c0269acd36e. This exact boundary homotopy is the source-faithful geometric step in the strand-extension conjugation proof.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_strand_extension_v1
open BraidsLinksMCG TarchaBraids TarchaBraids.StrandExtension

theorem BraidsLinksMCG.extensionBoundaryHomotopy_inline_child_v2 (n : ℕ) (j : Fin n) :
    (((((standardLoop (n + 1) j.castSucc).map
          (configIncl (n + 1)).continuous).cast
        (configIncl_base (n + 1)).symm (configIncl_base (n + 1)).symm).map
        (configProj (n + 2)).continuous).trans
      (halfTwistLoop (n + 2) (Fin.last n))).Homotopic
      ((halfTwistLoop (n + 2) (Fin.last n)).trans
        ((((((standardLoop n j).map (configIncl n).continuous).cast
          (configIncl_base n).symm (configIncl_base n).symm).map
            (configProj (n + 1)).continuous).map
          (TarchaBraids.StrandExtension.addU (n + 1)).continuous).cast
          (TarchaBraids.StrandExtension.addU_base (n + 1)).symm
          (TarchaBraids.StrandExtension.addU_base (n + 1)).symm)) := by sorry
