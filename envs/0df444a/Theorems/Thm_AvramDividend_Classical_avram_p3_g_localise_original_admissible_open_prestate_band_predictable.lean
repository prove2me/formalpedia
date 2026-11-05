-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_admissible_open_prestate_band_predictable
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_admissible_open_prestate_band_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:18:02.765684+00:00
-- url     : https://prove2.me/theorems/913dc24c-9aa6-497c-8bdd-2d76309f3623
-- title:
--   All original admissible pre-reserve open bands are strongly predictable
-- statement:
--   For the actual original x+X.X-rightLimit D reserve with IsAdmissibleLe control, the pre-payment reserve left-limit belongs to any chosen open interval Ioo a b in a right-continuous predictable measurable set. In particular all deterministic rational interior strips from the countable P3-G exhaustion have source-exact predictable membership; no regularity at the zero or cap boundary is presumed.
-- source:
--   Composes Proved original pre-reserve strongly predictable 94ee9994 and the projection hD.1.1, with ordinary measurable preimages of open real intervals.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_admissible_open_prestate_band_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (a b : ℝ) :
    MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω |
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈
          Ioo a b} := by sorry
