-- Prove2me | Theorems.Thm_BKAR_Forest_orderedSimplexIntegralAux_eq_setIntegral_orderedFinSimplexWithTop_of_continuous
-- name    : BKAR.Forest.orderedSimplexIntegralAux_eq_setIntegral_orderedFinSimplexWithTop_of_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:13:31.483681+00:00
-- url     : https://prove2.me/theorems/2d9c9618-33c4-4b95-a3bd-615b29b36f80
-- title:
--   Forest: ordered Simplex Integral Aux eq set Integral ordered Fin Simplex With Top of continuous
-- statement:
--   Finite-dimensional analytic core of the simplex-sector conversion: for
--   continuous integrands, the recursive
--   ordered simplex integral is the set integral over the closed finite ordered
--   simplex with the same top bound.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L650-L727
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L650-L727

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]

theorem BKAR.Forest.orderedSimplexIntegralAux_eq_setIntegral_orderedFinSimplexWithTop_of_continuous
    {top : ℝ} (htop : 0 ≤ top) :
    ∀ (order : List (Edge V)) (G : (Fin order.length → ℝ) → ℝ),
      Continuous G →
        orderedSimplexIntegralAux top order
          (fun ts => G (fun i : Fin order.length => ts.getD i.val 0)) =
        ∫ xs in orderedFinSimplexWithTop top order.length, G xs
  := by sorry
