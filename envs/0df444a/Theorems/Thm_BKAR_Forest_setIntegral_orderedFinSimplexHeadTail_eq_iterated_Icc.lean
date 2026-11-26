-- Prove2me | Theorems.Thm_BKAR_Forest_setIntegral_orderedFinSimplexHeadTail_eq_iterated_Icc
-- name    : BKAR.Forest.setIntegral_orderedFinSimplexHeadTail_eq_iterated_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:13:45.128079+00:00
-- url     : https://prove2.me/theorems/0e6dee30-9f67-4a88-9a87-163a986b1200
-- title:
--   Forest: set Integral ordered Fin Simplex Head Tail eq iterated Icc
-- statement:
--   Fubini split for the head-tail finite ordered simplex sector.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L314-L376
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L314-L376

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.setIntegral_orderedFinSimplexHeadTail_eq_iterated_Icc
    (top : ℝ) (n : ℕ) (f : ℝ × (Fin n → ℝ) → ℝ)
    (hf : IntegrableOn f (orderedFinSimplexHeadTail top n)) :
    ∫ z in orderedFinSimplexHeadTail top n, f z =
      ∫ t in Set.Icc (0 : ℝ) top,
        ∫ us in orderedFinSimplexWithTop t n, f (t, us) := by sorry
