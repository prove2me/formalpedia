-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_dividend_strategy_predictable
-- name    : AvramDividend.Classical.avram_wave3_04_dividend_strategy_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:36:11.933822+00:00
-- url     : https://prove2.me/theorems/a4ef06a5-5b73-4d29-8e89-4a60aa82c3c5
-- title:
--   Every original adapted left-continuous dividend strategy is predictable
-- statement:
--   Every source IsDividendStrategy D, whose paths start at zero, are nondecreasing and continuous from the left, and which is adapted to the actual original filtration, is measurable for that filtration's predictable sigma algebra. No usual augmentation, right continuity of the filtration or atomic dividend restriction is imposed.
-- source:
--   Combine the canonical Proved AvramDividend.Classical.avram_wave3_04_predictable_rational_level (f9e7bb32-52ee-4d98-8a72-b1150ddc7ed4) with canonical Proved avram_wave3_04_leftcont_rational_density (706385b7-d262-4e4c-b098-44b69998ebc6) and IsDividendStrategy definition. A self-contained implementation duplicates both as private lemmas to avoid relying on unresolved import paths. Fulfils a genuine filtration measurability prerequisite in Avram Palmowski Pistorius (2007) Proposition 4(i) UBV stochastic verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal NNRat ENNReal

theorem AvramDividend.Classical.avram_wave3_04_dividend_strategy_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    @Measurable (ℝ≥0 × Ω) ℝ 𝓕.predictable inferInstance
      (fun p => D p.1 p.2) := by sorry
