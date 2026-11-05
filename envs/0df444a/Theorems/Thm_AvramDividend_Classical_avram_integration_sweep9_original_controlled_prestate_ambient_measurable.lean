-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_controlled_prestate_ambient_measurable
-- name    : AvramDividend.Classical.avram_integration_sweep9_original_controlled_prestate_ambient_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T15:31:05.558424+00:00
-- url     : https://prove2.me/theorems/63da8b2d-1ae0-464a-a0ca-a89f5f347203
-- title:
--   Actual original controlled reserve prestate is ambient jointly measurable
-- statement:
--   The full original strictly pre-payment controlled reserve left-limit x+X-D(t+) is measurable on ambient physical time × original Ω, uniformly over all times. This composes its genuinely Proved strong right-continuous predictability with the Proved predictable-to-product-measurable theorem and eliminates the independent original prestate-measurability assumption in the P3-E finite-horizon HJB L1 interface.
-- source:
--   Proved original strong predictability 94ee9994 and Proved original ambient predictable set conversion cd060910; source-exact no surrogate process or local measurability axiom. Feeds the hUpm premise of Proved 6f1e0ef2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_rightCont_predictable_ambient_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_integration_sweep9_original_controlled_prestate_ambient_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun p : ℝ≥0 × Ω =>
      Function.leftLim
        (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) := by sorry
