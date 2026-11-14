-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_uniform_ae_small_positive_error_integral_vanish
-- name    : AvramDividend.Classical.avram_bva_a22_uniform_ae_small_positive_error_integral_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:30:11.632205+00:00
-- url     : https://prove2.me/theorems/41dfda32-845e-4f76-8fc3-08732a238c81
-- title:
--   Original probability law: uniformly a.e. vanishing nonnegative integrable mesh errors vanish in expectation
-- statement:
--   For the original probability law P, any row-wise integrable nonnegative source error whose value is eventually no greater almost everywhere than every prescribed positive epsilon has expectation tending to zero. The eventual mesh index is a natural number and the almost-everywhere bound is uniform over sample paths for each fine row. The proof integrates each epsilon/2 upper bound and uses the order characterisation of convergence. This is the exact expected-error transfer needed for the original BV zero-reserve terminal-strip bound, avoiding a global generator L1 or dominated convergence of a random nonintegrable source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_uniform_ae_small_positive_error_integral_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (Err : ℕ → Ω → ℝ)
    (hErrI : ∀ m, Integrable (Err m) P)
    (hErrPos : ∀ m, ∀ᵐ ω ∂P, 0 ≤ Err m ω)
    (hSmall : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m : ℕ in atTop, ∀ᵐ ω ∂P, Err m ω ≤ ε) :
    Tendsto (fun m => ∫ ω, Err m ω ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
