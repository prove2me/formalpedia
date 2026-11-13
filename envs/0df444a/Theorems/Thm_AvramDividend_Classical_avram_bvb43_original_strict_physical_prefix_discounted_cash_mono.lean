-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb43_original_strict_physical_prefix_discounted_cash_mono
-- name    : AvramDividend.Classical.avram_bvb43_original_strict_physical_prefix_discounted_cash_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T18:48:01.199278+00:00
-- url     : https://prove2.me/theorems/f9673459-f3df-45e2-8d96-3819deb6deaf
-- title:
--   Original strictly stopped discounted Stieltjes cash increases along the uniform physical inner horizons
-- statement:
--   The original strict discounted cash on a uniform physical n mesh integrates over paymentTimes σ intersect (-∞,T-T/(n+2)). The cutoff grows with n for T>0. Prove the cutoff ordering by positive-denominator division, then apply pinned Mathlib MeasureTheory.lintegral_mono_set to the exact intersection. This preserves singular Stieltjes atoms, the time-zero right payment, the strict ruin mask, and the endpoint convention; it holds for every dividend measure μ and does not rely on continuity, a surrogate source process or negative-mark assumptions. Used to compare a fixed cash prefix n with refining compensation grid k in bvb42.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_mono_set and source original dividend paymentTimes; Avram et al Proposition 4(i) strict cash convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb43_original_strict_physical_prefix_discounted_cash_mono
    (T : ℝ) (hT : 0 < T) (q : ℝ) (σ : ℝ≥0∞)
    (μ : Measure ℝ) (n k : ℕ) (hnk : n ≤ k) :
    (∫⁻ t in paymentTimes σ ∩ Iio (T - T / ((n : ℝ) + 2)),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤
    (∫⁻ t in paymentTimes σ ∩ Iio (T - T / ((k : ℝ) + 2)),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) := by sorry
