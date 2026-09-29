-- Prove2me | Theorems.Thm_BraidsLinksMCG_extensionBoundaryHomotopy_inline_child_v4
-- name    : BraidsLinksMCG.extensionBoundaryHomotopy_inline_child_v4
-- status  : Open
-- author  : @WillR
-- created : 2026-09-23T20:08:34.920744+00:00
-- url     : https://prove2.me/theorems/39872516-612f-4cb5-9ca6-4ee965218a2f
-- title:
--   The boundary homotopy in the braid-group conjugation order
-- statement:
--   The final half-twist followed by the projected included standard loop is homotopic to the strand-added standard loop followed by the final half-twist; this is the path order required by the parent conjugation identity.
-- source:
--   Correctly oriented theorem-only boundary-homotopy child, derived by reversing the square homotopy to match FundamentalGroup.mul_def.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_strand_extension_v1
open BraidsLinksMCG TarchaBraids TarchaBraids.StrandExtension

theorem BraidsLinksMCG.extensionBoundaryHomotopy_inline_child_v4 (n : ℕ) (j : Fin n) :
    ((halfTwistLoop (n + 2) (Fin.last n)).trans
      (((((standardLoop (n + 1) j.castSucc).map
          (configIncl (n + 1)).continuous).cast
        (BraidsLinksMCG.configIncl_base (n + 1)).symm
        (BraidsLinksMCG.configIncl_base (n + 1)).symm).map
        (configProj (n + 2)).continuous))).Homotopic
      (((((((standardLoop n j).map (configIncl n).continuous).cast
          (BraidsLinksMCG.configIncl_base n).symm
          (BraidsLinksMCG.configIncl_base n).symm).map
            (configProj (n + 1)).continuous).map
          (TarchaBraids.StrandExtension.addU (n + 1)).continuous).cast
          (TarchaBraids.StrandExtension.addU_base (n + 1)).symm
          (TarchaBraids.StrandExtension.addU_base (n + 1)).symm).trans
        (halfTwistLoop (n + 2) (Fin.last n))) := by sorry
