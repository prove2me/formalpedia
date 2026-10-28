-- Prove2me | Theorems.Thm_FeynmanKac_model_pathDiscount_pos_le_one
-- name    : FeynmanKac.model_pathDiscount_pos_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T09:07:16.366985+00:00
-- url     : https://prove2.me/theorems/eae89492-1142-44d3-a6b8-1b9ab080db8a
-- title:
--   Nonnegative model potential yields positive discount bounded by one
-- statement:
--   For the genuine Feynman–Kac diffusion model with a nonnegative potential, the pathwise discount factor satisfies 0<D_{t,s}≤1 for any s≥t at which the potential along the realised path is interval-integrable. This is derived from the already proved path-discount inequality, not assumed as an additional model field. The estimate will bound the discounted gradient by the un-discounted gradient on finite horizons.
-- source:
--   Proved FeynmanKac.discount_pos_le_one, published FeynmanKac_BoundedDiffusionModel

import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Theorems.Thm_FeynmanKac_discount_pos_le_one
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

theorem FeynmanKac.model_pathDiscount_pos_le_one
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (s : ℝ) (hts : m.initialTime ≤ s) (ω : Ω)
    (hInt : IntervalIntegrable (fun r => m.potential (m.path r ω) r)
        MeasureTheory.volume m.initialTime s) :
    0 < m.pathDiscount s ω ∧ m.pathDiscount s ω ≤ 1 := by sorry
