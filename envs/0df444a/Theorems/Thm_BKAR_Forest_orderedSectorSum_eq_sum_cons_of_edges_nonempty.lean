-- Prove2me | Theorems.Thm_BKAR_Forest_orderedSectorSum_eq_sum_cons_of_edges_nonempty
-- name    : BKAR.Forest.orderedSectorSum_eq_sum_cons_of_edges_nonempty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:48:34.196423+00:00
-- url     : https://prove2.me/theorems/61a535f6-c53a-54eb-a144-c6feebdba72d
-- title:
--   Forest: ordered Sector Sum eq sum cons of edges nonempty
-- statement:
--   For a nonempty forest, the ordered-sector sum splits by first edge and then by
--   an ordering of the remaining edge set.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L643-L652
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L643-L652

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedSectorSum_eq_sum_cons_of_edges_nonempty
    (F : Forest V) (hF : F.edges.Nonempty)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedSectorSum ρ =
      Finset.sum F.edges.attach
        (fun e => Finset.sum (edgeSetOrders (F.edges.erase e.val))
          (fun order => F.orderedContribution (e.val :: order) ρ)) := by sorry
