-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_natural_horizons_suffice_for_stieltjes_bound
-- name    : AvramDividend.Classical.avram_wave7_11_natural_horizons_suffice_for_stieltjes_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:57:58.346817+00:00
-- url     : https://prove2.me/theorems/e9e91a92-6ba4-4116-9adf-646361d14b52
-- title:
--   Integer-horizon discounted Stieltjes estimates imply the bound at every real horizon
-- statement:
--   On the canonical sample space and original Stieltjes dividend measure, a uniform expected discounted payout bound proved at every natural-number terminal time extends to each real terminal time, including times below zero. This gives a finite-grid-to-real-horizon reduction for the UBV original-process proof, with the time-zero dividend atom retained exactly.
-- source:
--   The Archimedean theorem exists_nat_gt at pinned Mathlib revision 0df444a supplies a natural n≥T. Inclusion of the original paymentTimes∩Iic sets and twice-applied ENNReal lintegral monotonicity conclude. Source-faithful deterministic sublemma for AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_unbounded_variation (cc518136...).

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_natural_horizons_suffice_for_stieltjes_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞) (q : ℝ) (B : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ B)
    (T : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ B := by sorry
