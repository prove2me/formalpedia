-- Prove2me | Theorems.Thm_BKAR_Forest_orderedFinSimplexWithTop_succ_eq_piFinSuccAbove_preimage_headTail
-- name    : BKAR.Forest.orderedFinSimplexWithTop_succ_eq_piFinSuccAbove_preimage_headTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:00:58.99499+00:00
-- url     : https://prove2.me/theorems/1158e0c3-2556-44de-b2cf-7f169a4178d3
-- title:
--   Forest: ordered Fin Simplex With Top succ eq pi Fin Succ Above preimage head Tail
-- statement:
--   The `piFinSuccAbove` coordinate split identifies the `(n+1)`-dimensional
--   ordered simplex with its head-tail product-coordinate sector.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L253-L273
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L253-L273

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedFinSimplexWithTop_succ_eq_piFinSuccAbove_preimage_headTail
    (top : ℝ) (n : ℕ) :
    orderedFinSimplexWithTop top (n + 1) =
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) 0) ⁻¹'
        orderedFinSimplexHeadTail top n := by sorry
