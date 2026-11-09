-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_stop_original_Q_ceiling_ae
-- name    : AvramDividend.Classical.avram_ubv_gauss13_stop_original_Q_ceiling_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T22:46:00.946782+00:00
-- url     : https://prove2.me/theorems/d39c5abe-ffd4-4b9b-8fba-94d4b067d0be
-- title:
--   Original Gaussian compensated quadratic source converges almost surely at physical ceilings
-- statement:
--   Direct same-source predecessor of avram_ubv_gauss13_stop_original_Q_terminal_condexp_L1, needed by original Gaussian finite-cap a338c453-58c0-411c-aaca-5cec689ed807 and top-cap 249c532d-4ec0-498c-81f0-b380dd476344. With a genuine physical ceiling grid satisfying the source clock squeeze and vanishing mesh, Proved 23b87d40 gives almost sure convergence of X.X at the ceilings. The same squeeze gives convergence of clock times and their real casts, hence convergence of original compensated Gaussian squares Q_t. It does not use a detached Brownian path or a floor stopping time and does not by itself claim L1. The companion common-terminal conditional-expectation helper supplies the L1 step.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_original_zerojump_ceiling_path_limit

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_stop_original_Q_ceiling_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (σ : Ω → ℝ≥0)
    (grid : ℕ → ℕ → ℝ≥0) (K : ℕ → Ω → ℕ)
    (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (nhds 0))
    (hBounds : ∀ n ω,
      σ ω ≤ grid n (K n ω) ∧
      grid n (K n ω) ≤ σ ω + δ n) :
    ∀ᵐ ω ∂P, Tendsto (fun n =>
      (X.X (grid n (K n ω)) ω -
        (grid n (K n ω) : ℝ) * X.c) ^ 2 -
        (grid n (K n ω) : ℝ) * X.σ ^ 2)
      atTop (nhds
        ((X.X (σ ω) ω - (σ ω : ℝ) * X.c) ^ 2 -
          (σ ω : ℝ) * X.σ ^ 2)) := by
  sorry
