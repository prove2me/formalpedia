-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_disjoint_cross_integral_zero
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_disjoint_cross_integral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:02:20.952236+00:00
-- url     : https://prove2.me/theorems/c412be42-4ae9-43a8-bd8c-7fded869270c
-- title:
--   Disjoint original Gaussian source cells have exact zero covariance
-- statement:
--   Two disjoint deterministic drift-centred increments of the actual original zero-jump spectrally negative Lévy source are genuinely integrable in product, and their true real expectation is exactly zero. Derive this off-diagonal L2 stochastic-integral isometry ingredient from the accepted conditional disjoint orthogonality and the pinned integral of conditional expectation. Requires no Gaussian scale positivity and no separately coupled Brownian copy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_disjoint_increment_L2_condExp_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_disjoint_cross_integral_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    let Y₁ : Ω → ℝ := fun ω =>
      X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    let Y₂ : Ω → ℝ := fun ω =>
      X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c
    Integrable (Y₁ * Y₂) P ∧
      (∫ ω, Y₁ ω * Y₂ ω ∂P) = 0 := by
  sorry
