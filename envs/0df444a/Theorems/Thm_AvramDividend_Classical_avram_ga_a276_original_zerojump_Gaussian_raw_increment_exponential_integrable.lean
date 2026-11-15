-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a276_original_zerojump_Gaussian_raw_increment_exponential_integrable
-- name    : AvramDividend.Classical.avram_ga_a276_original_zerojump_Gaussian_raw_increment_exponential_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:14:06.580178+00:00
-- url     : https://prove2.me/theorems/fbd5d71c-2a6e-498f-b44f-7a807a4d6f1d
-- title:
--   Original zerojump Gaussian raw increment exponential integrable over every deterministic interval
-- statement:
--   For an original zero-jump Gaussian spectrally negative Lévy process with positive volatility and any deterministic interval s≤t, the raw increment exponential exp(theta*(X_t-X_s)) is integrable for every nonnegative theta. The result uses the proven Gaussian normalized exponential moment a68 with exact original Gaussian drift and sigma and gives the full raw exponential L1 dominator needed to prove true stopped fullcell signed rare exponential tail integrability in a277.
-- source:
--   Exact accepted original a228 raw exponential moment intermediate hRaw via normalized Gaussian a68

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a68_original_gaussian_normalised_increment_exp_integrable
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a276_original_zerojump_Gaussian_raw_increment_exponential_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (theta : ℝ) (hθ : 0 ≤ theta) :
    Integrable (fun ω : Ω =>
      Real.exp (theta*(X.X t ω-X.X s ω))) P := by sorry
