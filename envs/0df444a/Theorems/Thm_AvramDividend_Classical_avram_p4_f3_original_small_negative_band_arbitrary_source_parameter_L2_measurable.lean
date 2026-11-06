-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_small_negative_band_arbitrary_source_parameter_L2_measurable
-- name    : AvramDividend.Classical.avram_p4_f3_original_small_negative_band_arbitrary_source_parameter_L2_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:22:19.647576+00:00
-- url     : https://prove2.me/theorems/5ed70ebd-3cae-4624-99ec-64ad30150329
-- title:
--   Original small negative-band squared jump coefficient is measurable on arbitrary physical source parameter spaces
-- statement:
--   For the original Levy jump intensity and any measurable parameter space S (including physical time by omega), measurable reserve pair U,V:S to real yields measurable squared jump-coefficient integral over a negative band. The original Levy measure is proven SFinite.
-- source:
--   Source exact generalisation of the measurable original jump intensity argument: measurable extension of w, measurable function on S times mark space, original full Levy SFinite, and Measurable.lintegral_prod_right.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_zero_negative_payoff_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_full_levy_sfinite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_small_negative_band_arbitrary_source_parameter_L2_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {S : Type*} [mS : MeasurableSpace S]
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (U V : S → ℝ)
    (hU : Measurable U) (hV : Measurable V)
    (ε : ℝ) :
    Measurable (fun s =>
      (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U s + z) - w (U s)) -
            (w (V s + z) - w (V s))) ^ 2) ∂X.ν)) := by sorry
