-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB53_original_pointwise_cash_error_L1_squeeze
-- name    : AvramDividend.Classical.avram_gbB53_original_pointwise_cash_error_L1_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:15:47.621919+00:00
-- url     : https://prove2.me/theorems/9edd9f8b-d90b-4fd1-97e7-252453787591
-- title:
--   Original stopped cash pointwise error envelope with vanishing positive L1 implies physical-grid positive excess vanishes
-- statement:
--   For the true controlled cash source, a pathwise finite-grid residual bounded by an integrable error E_m whose positive L1 norm vanishes yields the original stopped cash positive-excess L1 limit. This separates a physical stopped Itô-Tanaka source inequality from the purely measure-theoretic squeeze step.
-- source:
--   A.e. monotonicity of maximum with zero, integral_mono_ae and squeeze_zero; no substitution of the original process and no assumption of cash positivity.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB53_original_pointwise_cash_error_L1_squeeze
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω)
    (F B : Ω → ℝ) (M E : ℕ → Ω → ℝ)
    (hSourceI : ∀ m, IntegrableOn
      (fun ω => max (F ω - M m ω - B ω) 0) A P)
    (hErrorI : ∀ m, IntegrableOn
      (fun ω => max (E m ω) 0) A P)
    (hSource : ∀ m, ∀ᵐ ω ∂(P.restrict A),
      F ω - M m ω - B ω ≤ E m ω)
    (hErrorL1 : Tendsto
      (fun m => ∫ ω in A, max (E m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto
      (fun m => ∫ ω in A, max (F ω - M m ω - B ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
