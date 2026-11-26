-- Prove2me | Theorems.Thm_BKAR_Forest_setIntegral_orderedFinSimplexWithTop_succ_eq_headTail
-- name    : BKAR.Forest.setIntegral_orderedFinSimplexWithTop_succ_eq_headTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:40.48081+00:00
-- url     : https://prove2.me/theorems/be6234e2-6b4f-4eb2-8c42-c1b0ab8da21a
-- title:
--   Forest: set Integral ordered Fin Simplex With Top succ eq head Tail
-- statement:
--   Measure transport from the `(n+1)`-coordinate finite simplex to its explicit
--   head-tail sector.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L280-L308
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L280-L308

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.setIntegral_orderedFinSimplexWithTop_succ_eq_headTail
    (top : ℝ) (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ) :
    ∫ ts in orderedFinSimplexWithTop top (n + 1), f ts =
      ∫ z in orderedFinSimplexHeadTail top n,
        f ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => ℝ) 0).symm z) := by sorry
