-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_disjoint_predictable_L2_bilinear_cross_condExp_zero
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_disjoint_predictable_L2_bilinear_cross_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:15:40.407233+00:00
-- url     : https://prove2.me/theorems/0978c1ba-692c-4360-a496-9987fb45f377
-- title:
--   Predictable two-cell original Gaussian source cross-product is L1 and conditionally zero from L2
-- statement:
--   For the same original zero-jump spectrally negative Lévy source and deterministic disjoint intervals s≤t≤u≤v, two F_u-past measurable predictable coefficients G,H with genuine L2 weighted source cells have an automatically integrable cross-product and conditional cross expectation zero given the original right-continuous F_u. This uses Hölder plus the already Proved arbitrary history-weighted disjoint cell cancellation. It is a source-faithful off-diagonal isometry input for predictable simple Gaussian stochastic integrals; sigma may vanish and no separate Brownian process is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_disjoint_history_weighted_cross_condExp_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_disjoint_predictable_L2_bilinear_cross_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v)
    (G H : Ω → ℝ)
    (hG : Measurable[𝓕.rightCont u] G)
    (hH : Measurable[𝓕.rightCont u] H)
    (hM1 : MemLp (fun ω =>
      G ω * (X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c)) 2 P)
    (hM2 : MemLp (fun ω =>
      H ω * (X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c)) 2 P) :
    let Y₁ : Ω → ℝ := fun ω =>
      X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    let Y₂ : Ω → ℝ := fun ω =>
      X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c
    Integrable ((G * Y₁) * (H * Y₂)) P ∧
      (P[(G * Y₁) * (H * Y₂) | 𝓕.rightCont u] =ᵐ[P]
        (fun _ => (0 : ℝ))) := by
  sorry
