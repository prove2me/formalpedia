-- Prove2me | Theorems.Thm_BKAR_Forest_setIntegral_orderedFinSimplexWithTop_succ_eq_iterated_Icc
-- name    : BKAR.Forest.setIntegral_orderedFinSimplexWithTop_succ_eq_iterated_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:12:23.621716+00:00
-- url     : https://prove2.me/theorems/e8d7f67b-2107-5d28-bd0b-95d3d1e3dec0
-- title:
--   Forest: set Integral ordered Fin Simplex With Top succ eq iterated Icc
-- statement:
--   Fubini split for the finite ordered simplex in `(n+1)` coordinates.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L398-L445
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L398-L445

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.setIntegral_orderedFinSimplexWithTop_succ_eq_iterated_Icc
    (top : ℝ) (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : IntegrableOn f (orderedFinSimplexWithTop top (n + 1))) :
    ∫ ts in orderedFinSimplexWithTop top (n + 1), f ts =
      ∫ t in Set.Icc (0 : ℝ) top,
        ∫ us in orderedFinSimplexWithTop t n, f (Fin.cons t us) := by sorry
