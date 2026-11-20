-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_finite_barrier_risk_strict_negative_at_physical_size2_first_mark
-- name    : AvramDividend.Classical.avram_jump6_A_original_finite_barrier_risk_strict_negative_at_physical_size2_first_mark
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:41:05.033622+00:00
-- url     : https://prove2.me/theorems/dfe5cb52-65dc-4468-8d17-6eb7c8485b5e
-- title:
--   Actual admissible finite-cap barrier reserve is strictly ruined at the first negative size-two physical mark
-- statement:
--   On a true original Brownian minus size-two marked-Poisson Lévy sample path with Gaussian tube |B_s|<1/4000 up to the mark time σ and at least one physical negative mark by σ, the finite barrier strategy at capital 1/10 and barrier 1/5 pays zero because all X_s remain below the 1/10 threshold. The actual controlled riskProcess X x barrierStrategy at σ is therefore x+B_σ−2N_σ<0, a genuinely ruin-causing original stopped contact. This bridges the Proved physical first-mark event to the original ruinTime rather than using a synthetic terminal payoff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_finite_barrier_risk_strict_negative_at_physical_size2_first_mark
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B : ℝ≥0 → ℝ) (N : ℝ≥0 → ℕ)
    (σ : ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hMark : 1 ≤ N σ) :
    riskProcess X (1 / 10 : ℝ)
      (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) σ ω < 0 := by sorry
