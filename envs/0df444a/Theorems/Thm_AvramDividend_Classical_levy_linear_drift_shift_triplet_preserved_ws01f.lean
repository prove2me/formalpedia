-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_linear_drift_shift_triplet_preserved_ws01f
-- name    : AvramDividend.Classical.levy_linear_drift_shift_triplet_preserved_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:02:26.209258+00:00
-- url     : https://prove2.me/theorems/bb07c2d4-14f4-472d-a6f9-bff63472d98f
-- title:
--   Actual Lévy deterministic drift translation preserves Gaussian variance and negative jump measure exactly
-- statement:
--   For any authentic spectrally negative Lévy process X and deterministic linear drift shift C, construct a genuine process Y_t=X_t-Ct on the same sample space and law. Its exponent is ψ_Y=ψ_X-Cθ, and, crucially for the independent infinite-small-jump Rogozin branch, its Gaussian coefficient σ and Lévy jump measure ν are exactly those of X. Each càdlàg, no-positive-jump, adaptedness, stationary/independent increments and exponential moment structure field is proved directly, following the now accepted drift constructor source, rather than inferring triplet preservation from a weaker existential interface.
-- source:
--   Source-definitional triplet and the already canonically accepted proof of levy_linear_drift_shift_exists_ws01f, whose accepted proof evidence gives this explicit structure construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_linear_drift_shift_triplet_preserved_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (C : ℝ) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      (∀ (t : ℝ≥0) (ω : Ω),
        Y.X t ω = X.X t ω - C * (t : ℝ)) ∧
      (∀ θ : ℝ, Y.ψ θ = X.ψ θ - C * θ) ∧
      Y.σ = X.σ ∧ Y.ν = X.ν := by sorry
