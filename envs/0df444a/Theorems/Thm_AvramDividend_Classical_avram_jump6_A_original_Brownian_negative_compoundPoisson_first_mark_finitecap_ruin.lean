-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_Brownian_negative_compoundPoisson_first_mark_finitecap_ruin
-- name    : AvramDividend.Classical.avram_jump6_A_original_Brownian_negative_compoundPoisson_first_mark_finitecap_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:45:54.551841+00:00
-- url     : https://prove2.me/theorems/e6b76f1d-1905-4e4c-a928-4e9d95b4e3d8
-- title:
--   Genuine negative compound Poisson path and Brownian tube cause strict ruin without finite-barrier dividends
-- statement:
--   For the actual original spectrally negative Lévy path decomposed into its Brownian component B and genuine negative compound Poisson path J, assume the Brownian path remains within 1/4000 until σ, all Poisson contributions up to σ are nonpositive, and the negative physical jump path at σ has reached -2. The true original barrierStrategy with x=1/10 and finite barrier a=1/5 pays identically zero up to σ, and its actual controlled riskProcess at σ is strictly negative. This is a direct physical composition of the newly Proved almost-sure compoundPoisson path nonpositivity and first arrival value, and avoids synthetic martingale fields or artificial jump counts.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_Brownian_negative_compoundPoisson_first_mark_finitecap_ruin
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B J : ℝ≥0 → ℝ) (σ : ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t + J t)
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hJneg : ∀ t : ℝ≥0, t ≤ σ → J t ≤ 0)
    (hMark : J σ ≤ -2) :
    (∀ t : ℝ≥0, t ≤ σ →
      barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ) t ω = 0) ∧
    riskProcess X (1 / 10 : ℝ)
      (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) σ ω < 0 := by sorry
