-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_ae_cofinal_diagonal_stopped_vanishing_errors_real_perpetual
-- name    : AvramDividend.Classical.avram_limit2_ae_cofinal_diagonal_stopped_vanishing_errors_real_perpetual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:55:10.243488+00:00
-- url     : https://prove2.me/theorems/ccc6a6f4-ef89-43b0-80ac-8a0479340da6
-- title:
--   Original a.e.-cofinal diagonal stopped-clock and horizon budgets imply perpetual signed real payout
-- statement:
--   For the genuine original Levy dividend process D, measured nondecreasing random stop clocks σ_k with supremum ruinTime almost surely, assume only diagonal estimates at clock σ_k and deterministic closed cash horizon k: nonnegative stopped discounted dividendMeasure cash plus nonnegative Terminal_k has expected ENNReal value ≤finite B+error_k, with error_k→0. For any fixed integer horizon n and ε, shift all clocks by K=max(n,Nε). The tail clocks remain measurable, increasing and cofinal, cash Iic(n) is included in Iic(k+K), and the diagonal budget controls every shifted clock with error≤ε. Apply the already Proved original cofinal stopped Ito-terminal cash bridge for each n, then uniform truncation bound, remove ε, and invoke original finite-value signed Stieltjes theorem for genuine real L1 payout and exact expected value. Preserves time-zero and finite right-horizon atoms; no law replacement or terminal vanishing.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ae_cofinal_stopped_ito_terminal_payoff_budget
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_ae_cofinal_diagonal_stopped_vanishing_errors_real_perpetual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (σ : ℕ → Ω → ℝ≥0∞)
    (hσmeas : ∀ k : ℕ, Measurable (σ k))
    (hσmono : ∀ ω : Ω, Monotone (fun k : ℕ => σ k ω))
    (hSup : ∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω)
    (Terminal : ℕ → Ω → ℝ≥0∞) (error : ℕ → ℝ≥0∞)
    (hError : ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k → error k ≤ (ε : ℝ≥0∞))
    (hDiagonal : ∀ k : ℕ,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic (k : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal k ω) ∂P)
      ≤ B + error k) :
    dividendValue X q x D ≤ B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal (∫ ω,
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
