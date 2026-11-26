-- Prove2me | Theorems.Thm_BKAR_Forest_orderedSimplexIntegral_eq_setIntegral_orderedFinSimplex_of_continuous
-- name    : BKAR.Forest.orderedSimplexIntegral_eq_setIntegral_orderedFinSimplex_of_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:13:09.04319+00:00
-- url     : https://prove2.me/theorems/1c9f0f59-8c25-5068-bd5a-2b6c3330dceb
-- title:
--   Forest: ordered Simplex Integral eq set Integral ordered Fin Simplex of continuous
-- statement:
--   Unit-bound finite-dimensional analytic core of the simplex-sector conversion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L731-L746
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L731-L746

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]

theorem BKAR.Forest.orderedSimplexIntegral_eq_setIntegral_orderedFinSimplex_of_continuous
    (order : List (Edge V)) (G : (Fin order.length → ℝ) → ℝ)
    (hG : Continuous G) :
    orderedSimplexIntegral order
      (fun ts => G (fun i : Fin order.length => ts.getD i.val 0)) =
      ∫ xs in orderedFinSimplex order.length, G xs := by sorry
