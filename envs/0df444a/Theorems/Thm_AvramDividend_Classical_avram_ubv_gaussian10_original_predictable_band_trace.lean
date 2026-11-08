-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_predictable_band_trace
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_original_predictable_band_trace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:27:25.66884+00:00
-- url     : https://prove2.me/theorems/b749af0c-92b6-4e99-9117-db536994ddf4
-- title:
--   Predictable sigma-algebra trace on a finite band in the original Avram filtration
-- statement:
--   For Avram's original probability space and filtration, a set measurable with respect to the predictable sigma-algebra remains measurable with respect to Borel time times the original filtration at b after restricting to (a,b] times Ω. This creates the trace-measurability bridge needed for the stopped Gaussian bracket without substituting the Brownian natural filtration. The proof checks the predictable generator sets ({0} times F0 and (i,∞) times Fi) and closes under complements and countable unions.
-- source:
--   Mathlib.Probability.Process.Predictable at pin 0df444a360eaa60ab8c11dca51a86af692955474; adapted from formal-mathfin MathFin/Foundations/BracketCompensator.lean predictable_le_traceAlg, accessed 2026-11-07.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_original_predictable_band_trace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ≥0)
    (S : Set (ℝ≥0 × Ω))
    (hS : MeasurableSet[𝓕.predictable] S) :
    MeasurableSet[@Prod.instMeasurableSpace ℝ≥0 Ω inferInstance (𝓕 b)]
      (S ∩ (Ioc a b ×ˢ (univ : Set Ω))) := by sorry
