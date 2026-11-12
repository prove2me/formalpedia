-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger98_original_random_strict_open_mass_measurable
-- name    : AvramDividend.Classical.avram_gledger98_original_random_strict_open_mass_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:15:31.301897+00:00
-- url     : https://prove2.me/theorems/6f6d69c2-714e-4621-96f8-49d0862508cc
-- title:
--   Original Stieltjes dividend mass of a measurable random strict interval is measurable
-- statement:
--   For an original adapted dividend strategy and a measurable random endpoint, the undiscouted Stieltjes mass of its strict positive payment window is a measurable random variable. This lets the Gaussian stopped cash error be controlled in L1 by the already-proved discounted dividend envelope. The proof uses the existing global dividend-measure kernel and a measurable moving-set indicator, all on the original probability space.
-- source:
--   Smaller measurable original-source prerequisite for gledger39, gledger38 and gledger81.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger98_original_random_strict_open_mass_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ) :
    Measurable (fun ω : Ω =>
      dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))) := by sorry
