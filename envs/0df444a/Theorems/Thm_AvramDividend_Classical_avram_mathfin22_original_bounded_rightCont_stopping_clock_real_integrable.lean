-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_bounded_rightCont_stopping_clock_real_integrable
-- name    : AvramDividend.Classical.avram_mathfin22_original_bounded_rightCont_stopping_clock_real_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:48:01.05693+00:00
-- url     : https://prove2.me/theorems/72a9201e-42c5-436b-9fe3-cd0769c445c4
-- title:
--   Genuine right-continuous bounded stopping time is an integrable nonnegative real clock
-- statement:
--   Every original right-continuous filtration stopping time valued in WithTop nonnegative reals and uniformly bounded by a deterministic finite horizon T has an integrable real-valued untopA clock under a probability measure. Stopping-time measurability in the right-continuous filtration implies ambient measurability; measurable untopA and nonnegative-real-to-real coercion yield strong measurability. The WithTop bound implies the untopA clock lies in [0,T] pointwise and therefore is integrable by the bounded-integrable lemma. This eliminates a previously explicit clock L1 assumption from the original stopped true z-weighted signed Lévy mark integral proof without introducing unrelated stochastic hypotheses.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mathfin22_original_bounded_rightCont_stopping_clock_real_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hτbound : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0)) :
    Integrable (fun ω => ((τ ω).untopA : ℝ)) P := by sorry
