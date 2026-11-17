-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB32_original_risk_continuity_of_components
-- name    : AvramDividend.Classical.avram_gbB32_original_risk_continuity_of_components
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T18:44:18.936202+00:00
-- url     : https://prove2.me/theorems/b0a448be-5436-4599-aeaa-2e1919e2c18d
-- title:
--   Original riskProcess continuity follows from continuous Lévy and dividend components
-- statement:
--   Prove path-continuity of the exact original riskProcess whenever the original Levy process and original dividend strategy are continuous, using the source definition riskProcess = initial reserve + X.X - D. No strengthened assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory ProbabilityTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB32_original_risk_continuity_of_components
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hX : ∀ ω, Continuous (fun t : ℝ≥0 => X.X t ω))
    (hD : ∀ ω, Continuous (fun t : ℝ≥0 => D t ω)) :
    ∀ ω, Continuous (fun t : ℝ≥0 => riskProcess X x D t ω) := by sorry
