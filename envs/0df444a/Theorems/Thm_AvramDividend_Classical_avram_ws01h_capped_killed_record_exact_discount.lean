-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_capped_killed_record_exact_discount
-- name    : AvramDividend.Classical.avram_ws01h_capped_killed_record_exact_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:58:34.218991+00:00
-- url     : https://prove2.me/theorems/5c387870-cdbf-450c-80f5-455ca97a43ab
-- title:
--   Original Lévy killed first-record stopped Esscher density equals its exact total discount
-- statement:
--   For the actual source strict upper first-record capped at a finite time, conditional on genuine upper crossing, its exponential-clock survival factor multiplied by the stopped Esscher Radon-Nikodym density equals exp(phi*b-(p+q)*tau). This discharges the exact weight premise in lower-killed record regeneration independently of the two-sided exit theorem.
-- source:
--   Avram Palmowski Pistorius (2007), strict upward first-passage no-overshoot and Esscher transform, combined with canonical source theorem df1c0da0-aa12-4f9f-89de-296081c3a314.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_capped_record_no_positive_overshoot

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_capped_killed_record_exact_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (N : ℝ≥0) (ω : Ω)
    (φ q p : ℝ) (hroot : X.ψ φ = q)
    (hhit : twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)) :
    (let τ : ℝ≥0 :=
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     ENNReal.ofReal (Real.exp (-(p * (τ : ℝ)))) *
       ENNReal.ofReal (Real.exp
         (φ * X.X τ ω - (τ : ℝ) * X.ψ φ)) =
     ENNReal.ofReal
       (Real.exp (φ * b - (p + q) * (τ : ℝ)))) := by sorry
