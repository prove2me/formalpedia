-- Prove2me | Theorems.Thm_BraidsLinksMCG_extensionBoundaryHomotopy_child_v1
-- name    : BraidsLinksMCG.extensionBoundaryHomotopy_child_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-23T19:32:48.856469+00:00
-- url     : https://prove2.me/theorems/9ee02db6-1cca-4220-954f-cc77dcdc5247
-- title:
--   The strand-extension boundary paths are homotopic
-- statement:
--   The loop obtained by adding a stationary final strand and then performing the final half-twist is homotopic, relative to its basepoint, to performing the final half-twist first and then adding the strand to the original loop.
-- source:
--   Source-faithful geometric core extracted from the square-of-configurations argument for open target 2273a291-a4e8-43a8-b38b-527095999a64. The two boundary loops are the projected included standard loop and the addU image of the previous standard loop; the remaining child proof is precisely the square homotopy that exchanges their order with the final half-twist.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_strand_extension_v1

open BraidsLinksMCG TarchaBraids TarchaBraids.StrandExtension

noncomputable section

namespace BraidsLinksMCG

def extensionBoundaryLeftPath (n : ℕ) (j : Fin n) :
    Path (baseUnordered (n + 2)) (baseUnordered (n + 2)) where
  toFun t := configProj (n + 2)
    (configIncl (n + 1) (standardLoop (n + 1) j.castSucc t))
  continuous_toFun := (configProj (n + 2)).continuous.comp
    ((configIncl (n + 1)).continuous.comp (standardLoop (n + 1) j.castSucc).continuous)
  source' := by
    change configProj (n + 2) (configIncl (n + 1)
      (standardLoop (n + 1) j.castSucc 0)) = _
    rw [(standardLoop (n + 1) j.castSucc).source]
    simp [baseUnordered, configIncl_base]
  target' := by
    change configProj (n + 2) (configIncl (n + 1)
      (standardLoop (n + 1) j.castSucc 1)) = _
    rw [(standardLoop (n + 1) j.castSucc).target]
    simp [baseUnordered, configIncl_base]

def extensionBoundaryRightPath (n : ℕ) (j : Fin n) :
    Path (baseUnordered (n + 2)) (baseUnordered (n + 2)) where
  toFun t := addU (n + 1)
    (configProj (n + 1) (configIncl n (standardLoop n j t)))
  continuous_toFun := (addU (n + 1)).continuous.comp
    ((configProj (n + 1)).continuous.comp
      ((configIncl n).continuous.comp (standardLoop n j).continuous))
  source' := by
    change addU (n + 1) (configProj (n + 1)
      (configIncl n (standardLoop n j 0))) = _
    rw [(standardLoop n j).source]
    simp [baseUnordered, configIncl_base, addU_base, TarchaBraids.StrandExtension.sect_base]
  target' := by
    change addU (n + 1) (configProj (n + 1)
      (configIncl n (standardLoop n j 1))) = _
    rw [(standardLoop n j).target]
    simp [baseUnordered, configIncl_base, addU_base, TarchaBraids.StrandExtension.sect_base]

theorem extensionBoundaryHomotopy_child_v1 (n : ℕ) (j : Fin n) :
    ((extensionBoundaryLeftPath n j).trans
      (halfTwistLoop (n + 2) (Fin.last n))).Homotopic
      ((halfTwistLoop (n + 2) (Fin.last n)).trans
        (extensionBoundaryRightPath n j)) := by sorry

end BraidsLinksMCG
end
