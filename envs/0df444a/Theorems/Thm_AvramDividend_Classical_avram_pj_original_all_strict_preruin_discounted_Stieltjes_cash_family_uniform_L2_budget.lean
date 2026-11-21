-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_all_strict_preruin_discounted_Stieltjes_cash_family_uniform_L2_budget
-- name    : AvramDividend.Classical.avram_pj_original_all_strict_preruin_discounted_Stieltjes_cash_family_uniform_L2_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:26:07.133333+00:00
-- url     : https://prove2.me/theorems/42ada47c-f373-47ca-93bd-34a88c66ddcc
-- title:
--   Genuine original all strictly pre-ruin stopped discounted Stieltjes cash physical clock family shares a finite uniform L2 budget
-- statement:
--   For the genuine unbounded-variation spectrally negative Lévy process and admissible original dividend strategy, every strictly pre-ruin bounded family of stochastic physical clocks yields square-integrable full closed-horizon discounted Stieltjes cash. The second moment is bounded uniformly for all mesh refinements by the single finite number E[(x + runningSup of the original Lévy path over the fixed horizon)^2]. Use the proven original cash supremum bound and finite exponential moments, without assuming individual clock bounds that grow with the mesh.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_true_preruin_full_discounted_Stieltjes_cash_square_integrable_from_runningSup
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_strict_preruin_right_dividends_le_initial_plus_true_Levy_runningSup
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_real_stopped_cash_le_original_total_mass
import Theorems.Thm_AvramDividend_Classical_avram_ga_a35_original_dividend_rightLimit_nonnegative
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_all_UBV_true_fixedhorizon_runningSup_L1
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_unboundedvariation_finitehorizon_runningSup_square_integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_all_strict_preruin_discounted_Stieltjes_cash_family_uniform_L2_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (n : ℝ≥0) (ρ : ℕ → Ω → ℝ≥0)
    (hρle : ∀ k ω, ρ k ω ≤ n)
    (hρpre : ∀ k ω, (ρ k ω : ℝ≥0∞) <
      ruinTime X x D ω)
    (Cash : ℕ → Ω → ℝ)
    (hCash : ∀ k ω, Cash k ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Iic (ρ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hCashMeas : ∀ k, Measurable (Cash k)) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ k, Integrable (fun ω => (Cash k ω)^2) P ∧
        (∫ ω, (Cash k ω)^2 ∂P) ≤ B := by sorry
