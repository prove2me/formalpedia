-- Prove2me | Theorems.Thm_BKAR_Forest_setIntegral_orderedFinSimplexWithTop_succ_eq_iterated_interval
-- name    : BKAR.Forest.setIntegral_orderedFinSimplexWithTop_succ_eq_iterated_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:13:05.197681+00:00
-- url     : https://prove2.me/theorems/73717dd1-4915-430e-8069-6e476196b902
-- title:
--   Forest: set Integral ordered Fin Simplex With Top succ eq iterated interval
-- statement:
--   Interval-integral form of the one-step finite ordered-simplex Fubini split.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L451-L467
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L451-L467

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.setIntegral_orderedFinSimplexWithTop_succ_eq_iterated_interval
    {top : ℝ} (htop : 0 ≤ top) (n : ℕ)
    (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : IntegrableOn f (orderedFinSimplexWithTop top (n + 1))) :
    ∫ ts in orderedFinSimplexWithTop top (n + 1), f ts =
      ∫ t in 0..top,
        ∫ us in orderedFinSimplexWithTop t n, f (Fin.cons t us) := by sorry
