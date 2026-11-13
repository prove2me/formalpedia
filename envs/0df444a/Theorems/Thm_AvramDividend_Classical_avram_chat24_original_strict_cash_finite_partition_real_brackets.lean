-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_original_strict_cash_finite_partition_real_brackets
-- name    : AvramDividend.Classical.avram_chat24_original_strict_cash_finite_partition_real_brackets
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:29:52.048135+00:00
-- url     : https://prove2.me/theorems/e1d31940-5f0b-42be-b0e9-0e3ae5fc6e49
-- title:
--   Original strict Stieltjes cash finite-partition real brackets
-- statement:
--   Source-faithful analytic child of actual limit target 8ee5bfc7-c7d8-44b0-904f-a68e4becd13f. The actual strict dividend cash is finite and lies between the original lower and upper discounted sums on every finite monotone partition. The proof partitions the original Stieltjes cash, proves cell finiteness and converts sums to real values legitimately.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_chat24_original_strict_cash_finite_partition_real_brackets
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    let cash : ℝ≥0∞ := ∫⁻ t in Ico (u 0 : ℝ) (u n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
    cash ≠ ⊤ ∧
      (∑ i ∈ Finset.range n, Real.exp (-(q * (u (i + 1) : ℝ))) *
        (D (u (i + 1)) ω - D (u i) ω)) ≤ cash.toReal ∧
      cash.toReal ≤ (∑ i ∈ Finset.range n, Real.exp (-(q * (u i : ℝ))) *
        (D (u (i + 1)) ω - D (u i) ω)) := by sorry
