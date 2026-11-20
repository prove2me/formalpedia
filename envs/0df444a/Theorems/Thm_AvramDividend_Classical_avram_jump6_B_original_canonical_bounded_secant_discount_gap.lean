-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_bounded_secant_discount_gap
-- name    : AvramDividend.Classical.avram_jump6_B_original_canonical_bounded_secant_discount_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:13:55.353204+00:00
-- url     : https://prove2.me/theorems/991b08d1-d292-4d11-905d-071c19720b2e
-- title:
--   Original canonical grid discount mismatch bound for bounded cap-linear potential secants
-- statement:
--   For genuine dividendMeasure grid at the original stopped dividend strategy, when a sampled cap-linear potential secant is bounded above by L times the observed right-dividend increment, the error from shifting its exponential discount from left to right endpoints is at most L q Δ times total original right dividends. This pathwise bound is useful under compact spatial localisation without assuming finite jump activity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_canonical_bounded_secant_discount_gap
    {Ω : Type*} [MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (t : ℝ≥0) (j m : ℕ) :
    let Δ : ℝ≥0 := (1 : ℝ≥0) / ((j : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) t
    ∀ (L : ℝ), 0 ≤ L → ∀ (g : ℕ → ℝ),
      (∀ i < m, 0 ≤
        Real.exp (-(q * (v i : ℝ))) -
          Real.exp (-(q * (v (i+1) : ℝ)))) →
      (∀ i < m, g i ≤
        L * (rightLimit D (v (i+1)) ω - rightLimit D (v i) ω)) →
      (∑ i ∈ Finset.range m,
        (Real.exp (-(q * (v i : ℝ))) -
         Real.exp (-(q * (v (i+1) : ℝ)))) * g i) ≤
      L * (q * (Δ : ℝ) *
        (rightLimit D (v m) ω - rightLimit D (v 0) ω)) := by sorry
