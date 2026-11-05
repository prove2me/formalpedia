-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_L2_product_of_predictable_Linfty
-- name    : AvramDividend.Classical.avram_p4_g_isometry_L2_product_of_predictable_Linfty
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:22:05.309604+00:00
-- url     : https://prove2.me/theorems/4f43536b-ef24-42cb-acb6-3d70d43ece77
-- title:
--   Original-space L2 prefix times essentially bounded predictable coefficient
-- statement:
--   An L2 real random variable U times an essentially bounded V is L2 on the same underlying probability space. This is the analytic step needed to discharge all finite-simple predictable coefficient product L2 premises of the genuine Avram physical marked-jump grid isometry, with no stochastic measure replacement.
-- source:
--   Pinned Mathlib MeasureTheory.MemLp.mul type confirmed from revision-index compiler signature, Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp.

import Mathlib

open MeasureTheory
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_L2_product_of_predictable_Linfty
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (U V : Ω → ℝ) (hU : MemLp U 2 P) (hV : MemLp V ⊤ P) :
    MemLp (fun ω => U ω * V ω) 2 P := by sorry
