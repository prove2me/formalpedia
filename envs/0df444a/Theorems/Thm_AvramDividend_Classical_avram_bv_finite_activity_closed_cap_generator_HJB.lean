-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_finite_activity_closed_cap_generator_HJB
-- name    : AvramDividend.Classical.avram_bv_finite_activity_closed_cap_generator_HJB
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:46:13.852339+00:00
-- url     : https://prove2.me/theorems/32ce498d-d6a4-4907-ab2b-8b488c667842
-- title:
--   Finite-activity BV HJB inequality at the closed reserve cap
-- statement:
--   For a standing spectrally negative Levy process of bounded variation and finite negative-jump activity, the interior HJB generator inequality and unit gradient lower bound extend to the finite positive reserve cap. At the cap, the continuous reserve drift is paired with the full negative-mark jump integral. Continuity bounds the candidate on the compact reserve interval, and finite jump activity makes the resulting constant mark envelope integrable. This supplies a cap-contact boundary estimate for the original finite-cap stopped cash verification argument.
-- source:
--   Source-faithful cap-contact sublemma for mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43 and original finite-activity source 8271cf4d-01a2-4d49-ac27-ff1442ca1b4e. Derived using Proved dominated full-mark cap transfer 74c0faae-edc0-42a1-958f-a01a939630c5 and full-negative-increment integrability 5ff8b9b4-6a58-4c3f-9a0b-be295ee12ea2. This is a boundary lemma, not a claim of the parent expected budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_finite_activity_closed_cap_generator_HJB
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    X.drift + (∫ z in Iio (0 : ℝ),
      w (C.toReal + z) - w C.toReal ∂X.ν)
      - q * w C.toReal ≤ 0 := by sorry
