-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_compound_jumpCount_integrable
-- name    : AvramDividend.Classical.avram_a06_compound_jumpCount_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:21:12.65267+00:00
-- url     : https://prove2.me/theorems/8cb82ea4-b38e-451b-b3b4-ef7fdcefb50e
-- title:
--   Genuine compound-Poisson fixed-horizon jump count is integrable
-- statement:
--   The exact jump-count variable has a Poisson distribution at every nonnegative horizon. The Poisson law has an integrable natural-number identity, and measurable pushforward transfers the first moment.
-- source:
--   Public Proved distribution 5d293a54 and Poisson mean integrability b5167bf4, combined with new public count measurability.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_levy_foundations_compoundPoissonJumpCountLaw
import Theorems.Thm_ProbabilityTheory_integrable_id_poissonMeasure
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_jumpCount_measurable_public
open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_compound_jumpCount_integrable
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (t : ℝ≥0) :
    Integrable (fun ω => (LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) (t : ℝ) : ℝ)) P := by sorry
