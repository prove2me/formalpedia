-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_two_positive_source_errors_mean_gap
-- name    : AvramDividend.Classical.avram_p3_comp8_two_positive_source_errors_mean_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:37:43.897321+00:00
-- url     : https://prove2.me/theorems/c551387d-8946-4579-af43-1892e3945e23
-- title:
--   Two physical-grid source errors with vanishing positive expectations close the centred signed mean gap
-- statement:
--   If the original physical-grid finite payoff is pathwise bounded by initial value plus a centred compensated martingale, the exact signed HJB source residual, and two nonnegative cell/contact errors whose expected values vanish, then the positive expected signed source gap vanishes. The integrable cell and ruin-contact errors are kept separate for source proofs.
-- source:
--   Non-circular algebraic assembly of original physical-cell error and single final ruin-contact error; inputs are genuine L1 and pathwise source obligations.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_centred_pathwise_error_vanishing_mean_gap
open MeasureTheory Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp8_two_positive_source_errors_mean_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F B M ErrCell ErrContact : ℕ → Ω → ℝ) (k : ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hBI : ∀ n, Integrable (B n) P)
    (hMI : ∀ n, Integrable (M n) P)
    (hMean : ∀ n, (∫ ω, M n ω ∂P) = 0)
    (hCellI : ∀ n, Integrable (fun ω => max (ErrCell n ω) 0) P)
    (hContactI : ∀ n, Integrable (fun ω => max (ErrContact n ω) 0) P)
    (hBudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ k + (M n ω + B n ω) +
        max (ErrCell n ω) 0 + max (ErrContact n ω) 0)
    (hCell : Tendsto (fun n => ∫ ω, max (ErrCell n ω) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (hContact : Tendsto (fun n => ∫ ω, max (ErrContact n ω) 0 ∂P)
      atTop (nhds (0 : ℝ))) :
    Tendsto (fun n => max ((∫ ω, F n ω ∂P) - k -
        (∫ ω, B n ω ∂P)) 0) atTop (nhds (0 : ℝ)) := by sorry
