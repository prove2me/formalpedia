-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_positive_cutoff_epsilon_budget_full_ruin_expected_cash
-- name    : AvramDividend.Classical.avram_wave7_19_original_positive_cutoff_epsilon_budget_full_ruin_expected_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:37:14.688429+00:00
-- url     : https://prove2.me/theorems/3016d001-4947-4fb1-a07a-bca62c91b234
-- title:
--   Exact original ruin expected Stieltjes cash bound from arbitrarily small jump-truncation errors at stopped positive-time cutoffs
-- statement:
--   For any original spectrally negative Levy source and dividend strategy under its unchanged IsDividendStrategy hypothesis, finite horizon T and deterministic stopped clock n>T, suppose for every positive reciprocal lower-time cutoff k and arbitrarily small strictly positive NNReal epsilon the exact original discounted zero-atom-plus-cutoff expected Stieltjes reward is bounded by the budget plus epsilon (when the budget is finite). Then the full expected original pre-ruin finite-horizon discounted dividend cash is bounded by the budget exactly. This is the source-specific epsilon/jump-truncation limit passage using pinned ENNReal.le_of_forall_pos_le_add and the exact W7-19 full expected-cash MCT bridge. It requires no terminal uniform integrability, extra canonical moment hypotheses, atomlessness, or continuity at ruin. The actual stochastic Taylor error control and local Ito inequality must still be proved by the designated component owners.
-- source:
--   Pinned ENNReal.le_of_forall_pos_le_add (Mathlib.Data.ENNReal.Basic); W7-19 no-extra-hypothesis full expected cash bridge (published pending child 1b77d16f...); original W7-06/07 source L1 Taylor truncation controls; W7-08 original stopped Ito budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_positive_cutoff_epsilon_budget_full_ruin_expected_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ) (hT : 0 ≤ T)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (hn : ENNReal.ofReal T < (n : ℝ≥0∞))
    (budget : ℝ≥0∞)
    (hApprox : ∀ k : ℕ, ∀ ε : NNReal, 0 < ε → budget < ⊤ →
      (∫⁻ ω, ((∫⁻ t in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
        Icc (1 / ((k : ℝ) + 1)) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) ∂P) ≤
        budget + ENNReal.ofNNReal ε) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
