-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_gaussian_standing_and_unbounded_variation
-- name    : AvramDividend.Classical.positive_gaussian_standing_and_unbounded_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:26:46.005694+00:00
-- url     : https://prove2.me/theorems/2f5d468f-232f-4fc8-b93e-a9aeb72b289f
-- title:
--   Positive Gaussian coefficient implies Avram standing assumptions given first-moment integrability, and unbounded variation
-- statement:
--   For the canonical spectrally negative Lévy process, a positive Gaussian coefficient forces unbounded variation, excludes monotone paths and supplies the Gaussian alternative in condition (3.3). If the unit-time process is integrable, all the canonical standing hypotheses follow. This packages two important bridge obligations for the Brownian counterexample witness.
-- source:
--   Avram, Palmowski and Pistorius (2007), standing assumptions and (3.3); Prove2Me SpectrallyNegativeLevy definitions.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.positive_gaussian_standing_and_unbounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (hI : Integrable (X.X 1) P) :
    X.Standing ∧ ¬ X.BoundedVariation := by sorry
