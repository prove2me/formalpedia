-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_first_mem_support_edges_of_support_eq_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_first_mem_support_edges_of_support_eq_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:29:13.017863+00:00
-- url     : https://prove2.me/theorems/ca3622ee-4237-5508-a5f6-2a8271076023
-- title:
--   Active Terminal Branch Data: growth first mem support edges of support eq empty Start
-- statement:
--   The first edge of a selected terminal branch lies in its support fiber.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L315-L321
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L315-L321

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.growth_first_mem_support_edges_of_support_eq_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    {I : ForestIndex V} (hsupport : (data.growth e).support = I) :
    e.val ∈ I.edges := by sorry
