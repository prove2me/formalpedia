-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_survival_crossing_immediate_ruin_two_error_positive_L1_glue
-- name    : AvramDividend.Classical.avram_bva_a22_original_survival_crossing_immediate_ruin_two_error_positive_L1_glue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:04:38.693246+00:00
-- url     : https://prove2.me/theorems/898cd387-4239-426f-8c0f-63a61735dbd8
-- title:
--   Original BV C1 survival, positive ruin-crossing and immediate-ruin case bounds with two vanishing L1 envelopes imply the true source positive residual vanishes in L1
-- statement:
--   For the original Avram stopped BV C1 verification strategy, the source residual splits across strict survival past the horizon, positive ruin crossing within the horizon, and immediate ruin at zero. Abstract this exact source trichotomy into two measurable-event error envelopes ErrSurvival and ErrCrossing, each having nonnegative positive parts that are integrable and whose expected values tend to zero on the same original physical-grid index. Suppose the original residual Err has integrable positive part; on each event it is bounded by the respective positive source envelope, and on the complement (the immediate ruin event) the residual is nonpositive. Prove that the actual expected positive residual tends to zero by a pointwise maximum bound, Bochner integral monotonicity, linearity, and a squeeze. This is the missing logically sound final gluing argument from the existing original BVA-A22 survival/ruin C1 cash-error obligations, with no spatial reindexing and no assumption that the drift or jump error is identically zero. It is a valid reduction ingredient for theorem 73a56c2a, not a substitute for proving those source event error envelopes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Filter MeasureTheory
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_survival_crossing_immediate_ruin_two_error_positive_L1_glue
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Err ErrSurvival ErrCrossing : ℕ → Ω → ℝ)
    (Surv Cross : Ω → Prop)
    (hI : ∀ m, Integrable (fun ω => max (Err m ω) 0) P)
    (hIS : ∀ m, Integrable (fun ω => max (ErrSurvival m ω) 0) P)
    (hIC : ∀ m, Integrable (fun ω => max (ErrCrossing m ω) 0) P)
    (hS : ∀ m, ∀ᵐ ω ∂P, Surv ω →
      Err m ω ≤ max (ErrSurvival m ω) 0)
    (hC : ∀ m, ∀ᵐ ω ∂P, Cross ω →
      Err m ω ≤ max (ErrCrossing m ω) 0)
    (hZ : ∀ m, ∀ᵐ ω ∂P, ¬ Surv ω → ¬ Cross ω → Err m ω ≤ 0)
    (hLS : Tendsto (fun m => ∫ ω, max (ErrSurvival m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hLC : Tendsto (fun m => ∫ ω, max (ErrCrossing m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
