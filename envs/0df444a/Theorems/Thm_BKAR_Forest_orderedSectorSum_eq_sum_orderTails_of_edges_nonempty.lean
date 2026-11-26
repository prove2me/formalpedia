-- Prove2me | Theorems.Thm_BKAR_Forest_orderedSectorSum_eq_sum_orderTails_of_edges_nonempty
-- name    : BKAR.Forest.orderedSectorSum_eq_sum_orderTails_of_edges_nonempty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:48:51.420161+00:00
-- url     : https://prove2.me/theorems/e9e2e3bb-2c29-40f3-a5d0-69da4ec5bb59
-- title:
--   Forest: ordered Sector Sum eq sum order Tails of edges nonempty
-- statement:
--   Tail-pair version of `Forest.orderedSectorSum_eq_sum_cons_of_edges_nonempty`.
--   This is the indexing shape used by recursive branch assembly.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L658-L665
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L658-L665

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

theorem BKAR.Forest.orderedSectorSum_eq_sum_orderTails_of_edges_nonempty
    (F : Forest V) (hF : F.edges.Nonempty)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedSectorSum ρ =
      Finset.sum (edgeSetOrderTails F.edges)
        (fun x => F.orderedContribution (x.1.val :: x.2) ρ) := by sorry
