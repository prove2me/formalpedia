-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb48_original_zero_negative_mark_kernel_eq_intensity_value
-- name    : AvramDividend.Classical.avram_bvb48_original_zero_negative_mark_kernel_eq_intensity_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:47:50.649294+00:00
-- url     : https://prove2.me/theorems/84355106-ad20-4ae3-ba24-ae8ff46eff62
-- title:
--   Original BV finiteactivity zero reserve compensated negative mark kernel equals minus w(0) times negative jump intensity
-- statement:
--   For the true original Lévy negative-jump measure ν with finite negative jump intensity, and original candidate w zero for all negative reserves, compute the original zero-reserve generator kernel exactly: ∫_{z<0}[w(0+z)−w(0)]ν(dz)=−w(0)·ν((−∞,0)).real. This is a finite real integral and makes explicit why the original compensated term K cannot be dropped on a no-jump sample path. Uses set-integral equality on Iio0 and integral_const, with the same original ν.
-- source:
--   Original spectrally negative Lévy definition, Mathlib setIntegral_congr_fun and integral_const, finite ν negative mass.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb48_original_zero_negative_mark_kernel_eq_intensity_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (w : ℝ → ℝ)
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0) :
    (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν) =
      -(w 0) * (X.ν (Iio (0 : ℝ))).toReal := by sorry
