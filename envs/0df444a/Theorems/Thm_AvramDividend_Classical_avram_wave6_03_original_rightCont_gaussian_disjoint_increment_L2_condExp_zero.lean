-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_disjoint_increment_L2_condExp_zero
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_disjoint_increment_L2_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:46:38.162437+00:00
-- url     : https://prove2.me/theorems/7348ff03-76f3-4ab5-9ae5-daa7c68e9502
-- title:
--   Separated genuine Gaussian source increments are L2 and conditionally orthogonal
-- statement:
--   For the actual zero-jump spectrally negative Lévy source and deterministic nonoverlapping intervals [s,t] and [u,v] with s≤t≤u≤v, both drift-centred original-path increments are L2 and their cross-product is L1 with conditional expectation zero given the original right-continuous history at u. This is the off-diagonal orthogonality needed for finite-grid predictable Gaussian stochastic integral isometry, with arbitrary sigma including zero and no Brownian copy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_disjoint_increment_L2_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    let Y₁ : Ω → ℝ := fun ω =>
      X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    let Y₂ : Ω → ℝ := fun ω =>
      X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c
    MemLp Y₁ 2 P ∧ MemLp Y₂ 2 P ∧
    Integrable (Y₁ * Y₂) P ∧
      (P[Y₁ * Y₂ | 𝓕.rightCont u] =ᵐ[P] (fun _ => (0 : ℝ))) := by
  sorry
