-- Prove2me | Theorems.Thm_BKAR_Forest_orderedContribution_singleton_eq_orderedCubeSectorContribution
-- name    : BKAR.Forest.orderedContribution_singleton_eq_orderedCubeSectorContribution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:36:43.10307+00:00
-- url     : https://prove2.me/theorems/110ddbcc-8b87-4c02-baf9-fe3a64dacb07
-- title:
--   Forest: ordered Contribution singleton eq ordered Cube Sector Contribution
-- statement:
--   The simplex-sector conversion in the first nontrivial dimension: the nested
--   ordered-simplex integral for
--   a one-edge canonical order is exactly the set integral over the corresponding
--   closed ordered cube sector.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Singleton.lean#L168-L210
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Singleton.lean#L168-L210

import Mathlib.Data.List.NodupEquivFin
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedContribution_singleton_eq_orderedCubeSectorContribution
    (F : Forest V) {e : Edge V} (horder : [e] ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedContribution [e] ρ =
      F.orderedCubeSectorContribution [e] ρ := by sorry
