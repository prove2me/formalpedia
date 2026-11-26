-- Prove2me | Theorems.Thm_BKAR_Forest_orderedSimplexIntegral_singleton_eq_setIntegral_Icc
-- name    : BKAR.Forest.orderedSimplexIntegral_singleton_eq_setIntegral_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:36:21.629697+00:00
-- url     : https://prove2.me/theorems/385f2038-30e9-4c00-aaf6-454d7f872955
-- title:
--   Forest: ordered Simplex Integral singleton eq set Integral Icc
-- statement:
--   The one-dimensional ordered simplex integral is the set integral over `[0, 1]`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Singleton.lean#L112-L120
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Singleton.lean#L112-L120

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
omit [Fintype V]

theorem BKAR.Forest.orderedSimplexIntegral_singleton_eq_setIntegral_Icc
    (e : Edge V) (f : ℝ → ℝ) :
    orderedSimplexIntegral [e] (fun ts => f (ts.getD 0 0)) =
      ∫ t in Set.Icc (0 : ℝ) 1, f t := by sorry
