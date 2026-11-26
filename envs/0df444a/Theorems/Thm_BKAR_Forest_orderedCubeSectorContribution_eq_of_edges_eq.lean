-- Prove2me | Theorems.Thm_BKAR_Forest_orderedCubeSectorContribution_eq_of_edges_eq
-- name    : BKAR.Forest.orderedCubeSectorContribution_eq_of_edges_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:03:12.607193+00:00
-- url     : https://prove2.me/theorems/f31efd58-aa62-4cc8-b765-548d19cb4638
-- title:
--   Forest: ordered Cube Sector Contribution eq of edges eq
-- statement:
--   Closed ordered cube-sector contributions are invariant under replacing a `Forest` representative
--   by another `Forest` representative with the same underlying edge set.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CubeFold.lean#L28-L43
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CubeFold.lean#L28-L43

import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Definitions.Def_BKAR_OrderedAssembly_CubeFold
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedCubeSectorContribution_eq_of_edges_eq
    (F G : Forest V) (hedges : F.edges = G.edges)
    {order : List (Edge V)}
    (hForder : order ∈ F.edgeOrders) (hGorder : order ∈ G.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedCubeSectorContribution order ρ =
      G.orderedCubeSectorContribution order ρ := by sorry
