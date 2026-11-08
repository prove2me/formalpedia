-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_eventual_negative_budget_forbids_zero_error
-- name    : AvramDividend.Classical.avram_bv_residual9_eventual_negative_budget_forbids_zero_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:04:16.953402+00:00
-- url     : https://prove2.me/theorems/4e652940-d04b-432a-a43e-a0912a34b87b
-- title:
--   An eventually negative original residual expectation forbids a vanishing expected positive error even without cash integrability
-- statement:
--   If a source-exact stopped budget has mean-zero integrable M and integrable signed B, and the original cash plus terminal is nonnegative, an eventually strict expected deficit E B ≤ -w(x)-epsilon forces a positive error expectation bounded away from zero. Only the pointwise nonnegative-budget inequality is needed; no integrability of the cash payoff is required. Eventual means n sufficiently large, matching the non-refining original countermodel whose fixed cell exists for n≥1.
-- source:
--   AVRAM BV-RESIDUAL9 round-three Standing-valid continuous-jump disproof criterion

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_eventual_negative_budget_forbids_zero_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (a ε : ℝ) (hε : 0 < ε)
    (M B E : ℕ → Ω → ℝ)
    (hM : ∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0)
    (hB : ∀ n, Integrable (B n) P)
    (hE : ∀ n, Integrable (E n) P)
    (hBneg : ∀ᶠ n in atTop, (∫ ω, B n ω ∂P) ≤ -a - ε)
    (hbudget : ∀ n, ∀ᵐ ω ∂P,
      0 ≤ a + M n ω + B n ω + E n ω) :
    ¬ Tendsto (fun n => ∫ ω, E n ω ∂P) atTop (nhds (0 : ℝ)) := by sorry
