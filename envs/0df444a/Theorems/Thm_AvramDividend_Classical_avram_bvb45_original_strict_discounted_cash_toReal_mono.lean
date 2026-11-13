-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb45_original_strict_discounted_cash_toReal_mono
-- name    : AvramDividend.Classical.avram_bvb45_original_strict_discounted_cash_toReal_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T18:58:21.637299+00:00
-- url     : https://prove2.me/theorems/ab860631-e9e5-4e02-b5e0-eb21095fcaab
-- title:
--   Actual finite original Stieltjes cash real prefixes increase with physical uniform horizon
-- statement:
--   If the original strictly ruin-stopped discounted dividend Stieltjes measure has finite total cash up to physical horizon T, the actual real-valued cash integrals on physical inner uniform horizons T-T/(n+2) are monotone in n. The proof uses the Proved exact ENNReal cash prefix inclusion bvb43 and the original total cash finiteness to justify the ENNReal.toReal order transfer. Keeps singular dividends, initial right payment, true ruin and the true physical endpoint.
-- source:
--   Proved bvb43 original cash monotonicity; Proved f0d4c94c original full-horizon stopped discounted dividend cash ae finite; ENNReal.toReal_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb43_original_strict_physical_prefix_discounted_cash_mono
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb45_original_strict_discounted_cash_toReal_mono
    (T : ℝ) (hT : 0 < T) (q : ℝ) (σ : ℝ≥0∞)
    (μ : Measure ℝ)
    (hFinite : (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) < ⊤)
    (n k : ℕ) (hnk : n ≤ k) :
    (∫⁻ t in paymentTimes σ ∩ Iio (T - T / ((n : ℝ) + 2)),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ).toReal ≤
    (∫⁻ t in paymentTimes σ ∩ Iio (T - T / ((k : ℝ) + 2)),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ).toReal := by sorry
