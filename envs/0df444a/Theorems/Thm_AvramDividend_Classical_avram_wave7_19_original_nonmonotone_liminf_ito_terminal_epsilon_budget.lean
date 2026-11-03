-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_nonmonotone_liminf_ito_terminal_epsilon_budget
-- name    : AvramDividend.Classical.avram_wave7_19_original_nonmonotone_liminf_ito_terminal_epsilon_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:29:29.1982+00:00
-- url     : https://prove2.me/theorems/d4351c93-e20b-4fa0-81ac-4bd4cf833521
-- title:
--   Original nonmonotone stopped Ito with terminal payoffs and vanishing jump errors implies full finite-horizon ruin cash
-- statement:
--   For the original spectrally negative Lévy process with IsDividendStrategy, suppose W7-18's measurable stopped clocks have P-a.s. lower tail limit equal to ruin. The W7-05/06/07 local stopped Ito estimates may include nonnegative ENNReal terminal values and arbitrarily small NNReal jump-truncation errors. Discard terminal payoffs, use ENNReal.le_of_forall_pos_le_add at each fixed clock to erase the error, then apply W7-19's generic nonmonotone a.s. liminf boundary passage. The resulting full expected original Stieltjes dividend cash bound preserves time-zero right payment and excludes the positive ruin-time right payment, with no UI or canonical hypothesis changes.
-- source:
--   Generic source-specific nonmonotone limit theorem 5b95b760-17b7-4b4a-a03c-5c01a98b69b3 when Proved; source Ito terminal nonnegativity and accepted ENNReal small-jump error removal 3016d001-4947-4fb1-a07a-bca62c91b234.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_nonmonotone_liminf_ito_terminal_epsilon_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n : ℕ, Measurable (τ n))
    (hLiminf : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω) = ruinTime X x D ω)
    (Terminal : NNReal → ℕ → Ω → ℝ≥0∞) (budget : ℝ≥0∞)
    (hStopped : ∀ (n : ℕ) (ε : NNReal), 0 < ε → budget < ⊤ →
      (∫⁻ ω, ((∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
        Terminal ε n ω) ∂P) ≤ budget + ENNReal.ofNNReal ε) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
