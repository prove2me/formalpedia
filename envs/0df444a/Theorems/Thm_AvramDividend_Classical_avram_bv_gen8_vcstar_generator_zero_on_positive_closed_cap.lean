-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_vcstar_generator_zero_on_positive_closed_cap
-- name    : AvramDividend.Classical.avram_bv_gen8_vcstar_generator_zero_on_positive_closed_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:38:57.08845+00:00
-- url     : https://prove2.me/theorems/0de73404-12fb-4bbe-905a-4722946cc8c2
-- title:
--   Unconditional BV cstar generator harmonicity on the full positive closed barrier interval
-- statement:
--   For the original spectrally negative Levy process of bounded variation, the candidate value function is generator-integrable and q-harmonic at every positive reserve up to and including the barrier. This joins the existing strict-interior and exact barrier certificates without any generator assumption above the barrier.
-- source:
--   Follows exactly from the Proved b196c9ff interior BV generator theorem and 0458283a unconditional positive cap point theorem via trichotomy.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_gen8_vcstar_generator_zero_on_positive_closed_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W) :
    ∀ y : ℝ, 0 < y → y ≤ (cstar W).toReal →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y = 0 := by sorry
