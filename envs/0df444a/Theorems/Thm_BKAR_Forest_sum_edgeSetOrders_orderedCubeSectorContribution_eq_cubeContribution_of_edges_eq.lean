-- Prove2me | Theorems.Thm_BKAR_Forest_sum_edgeSetOrders_orderedCubeSectorContribution_eq_cubeContribution_of_edges_eq
-- name    : BKAR.Forest.sum_edgeSetOrders_orderedCubeSectorContribution_eq_cubeContribution_of_edges_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:03:33.885636+00:00
-- url     : https://prove2.me/theorems/6c1853e7-728c-4de1-a388-c220e7586182
-- title:
--   Forest: sum edge Set Orders ordered Cube Sector Contribution eq cube Contribution of edges eq
-- statement:
--   Transport the ordered-sector fold from a forest's own `edgeOrders` to the
--   canonical order set of any support index with the same edge set.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CubeFold.lean#L93-L101
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CubeFold.lean#L93-L101

import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Definitions.Def_BKAR_OrderedAssembly_CubeFold
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_edgeSetOrders_orderedCubeSectorContribution_eq_cubeContribution_of_edges_eq
    (F : Forest V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ)
    (hedges : F.edges = I.edges) :
    Finset.sum (edgeSetOrders I.edges)
      (fun order => F.orderedCubeSectorContribution order ρ) =
      F.cubeContribution ρ := by sorry
