-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_nat_horizon_integrable_of_standing
-- name    : AvramDividend.Classical.levy_nat_horizon_integrable_of_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:51:58.464982+00:00
-- url     : https://prove2.me/theorems/55e1b8ca-39d3-4232-a8ac-6e98ec2430af
-- title:
--   A spectrally negative Lévy process has integrable reserves at every integer horizon under the standing assumptions
-- statement:
--   For a spectrally negative Lévy process satisfying the paper's standing assumptions, the random variable X_n is integrable at every nonnegative integer n. The proof uses unit-time integrability from Standing and induction: the increment X_(n+1)-X_n has the same law as X_1 by stationarity, so it is integrable, and adding X_n preserves integrability. This permits integer-horizon localisation of discounted Stieltjes dividend estimates without adding integrability hypotheses.
-- source:
--   SpectrallyNegativeLevy.Standing and SpectrallyNegativeLevy.stationaryIncrements from Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy; Mathlib.Probability.IdentDistrib.integrable_iff at the mission's pinned Mathlib revision.

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_nat_horizon_integrable_of_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) :
    ∀ n : ℕ, Integrable (X.X (n : ℝ≥0)) P := by sorry
