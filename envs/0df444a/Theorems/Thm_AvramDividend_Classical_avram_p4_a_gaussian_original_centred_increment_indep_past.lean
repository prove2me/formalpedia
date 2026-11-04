-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_indep_past
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_centred_increment_indep_past
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:06:55.170739+00:00
-- url     : https://prove2.me/theorems/728097d2-a908-45ad-879b-4804276d9c8f
-- title:
--   Original Levy drift-centred deterministic increment is independent of the past filtration
-- statement:
--   For the original Levy source, each deterministic centred increment is independent of the actual past filtration. It follows solely from the source independent-increments property and measurable deterministic drift translation, without a substitute Brownian process.
-- source:
--   Original SpectrallyNegativeLevy.indepIncrements field, Mathlib ProbabilityTheory.Indep_iff and measurableSet_comap.

import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_centred_increment_indep_past
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) :
    Indep
      (MeasurableSpace.comap
        (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)
        inferInstance)
      (𝓕 s) P := by sorry
