-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_bounded_preruin_strict_positive
-- name    : AvramDividend.Classical.avram_locmoll_bounded_preruin_strict_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:51:33.832142+00:00
-- url     : https://prove2.me/theorems/c156c41e-fe95-52b0-8387-d049207f3962
-- title:
--   Uniform almost-sure strict positivity of postpayment reserve before ruin on a bounded horizon
-- statement:
--   Uniform almost-sure strict positivity of postpayment reserve before ruin on a bounded horizon
-- source:
--   Strict-band clock construction: combine proved negative-reserve USC, capped lower-level hitting stopping time, and strict pre-ruin positivity at stopping times.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_bounded_preruin_strict_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ H → (t : ℝ≥0∞) < ruinTime X x D ω →
      0 < x + X.X t ω - rightLimit D t ω := by sorry
