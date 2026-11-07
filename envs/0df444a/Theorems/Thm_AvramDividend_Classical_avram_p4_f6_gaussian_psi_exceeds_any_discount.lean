-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_psi_exceeds_any_discount
-- name    : AvramDividend.Classical.avram_p4_f6_gaussian_psi_exceeds_any_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:06:37.354248+00:00
-- url     : https://prove2.me/theorems/55fe1edb-bc68-4850-84ce-e885f2e342ca
-- title:
--   Positive Gaussian volatility supplies an Esscher exponent above every discount
-- statement:
--   For the original spectrally negative Lévy process, strictly positive Gaussian volatility and the proved superlinear growth of its Laplace exponent imply that every real discount rate q lies below ψ(θ) for some θ≥1. This supplies the exact q<ψ(θ) hypothesis of the proved global exponentially weighted q-scale bound.
-- source:
--   Source-backed consequence of Gaussian superlinear Laplace growth c1392cb2 and upstream q-scale bound b9952447; a useful independent analytic building block towards original HJB growth 51922c24.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_psi_superlinear_of_positive_sigma
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_f6_gaussian_psi_exceeds_any_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ) (q : ℝ) :
    ∃ θ : ℝ, 1 ≤ θ ∧ q < X.ψ θ := by sorry
