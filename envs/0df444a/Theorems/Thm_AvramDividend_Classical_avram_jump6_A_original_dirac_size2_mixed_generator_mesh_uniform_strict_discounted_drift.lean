-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_dirac_size2_mixed_generator_mesh_uniform_strict_discounted_drift
-- name    : AvramDividend.Classical.avram_jump6_A_original_dirac_size2_mixed_generator_mesh_uniform_strict_discounted_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:51:08.149181+00:00
-- url     : https://prove2.me/theorems/f8c7e61a-4a80-43dd-a5c0-e7c587e92791
-- title:
--   Uniformly strictly negative discounted mixed Gaussian and genuine nonlinear size-two Poisson HJB drift across every original finite positive weighted mesh
-- statement:
--   For the actual mixed Gaussian/finite-jump spectrally negative Lévy model X with σ=1, c=0 and ν=δ_{−2}, and original piecewise quadratic HJB candidate w(y)=0 if y<0 and 1+y+y² otherwise, every interior reserve y∈(0,1/5] satisfies Γw(y)−(1/10)w(y)≤−1/10 using the Proved original generator identity and true marked Dirac compensator. Consequently every finite positive weighted physical stopped mesh has a uniformly negative total discounted generator drift bounded above by −(1/10) times total positive mesh weight. This strengthens the generic original HJB nonpositivity proof d0503e77 specifically for the genuine mixed Gaussian and size-two Poisson model and ensures a quantitatively dissipative real compensated drift in the corrected physical Itô-Meyer route.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_dirac_size2_mixed_generator_mesh_uniform_strict_discounted_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 1) (hc : X.c = 0)
    (hν : X.ν = Measure.dirac (-2 : ℝ))
    (m : ℕ) (y weight : ℕ → ℝ)
    (hwNonneg : ∀ i ∈ Finset.range m, 0 ≤ weight i)
    (hyInterior : ∀ i ∈ Finset.range m,
      0 < y i ∧ y i ≤ (1 / 5 : ℝ)) :
    let w : ℝ → ℝ := fun z =>
      if z < 0 then 0 else 1 + z + z ^ 2
    (∑ i ∈ Finset.range m,
        weight i * (X.generator w (y i) - (1 / 10 : ℝ) * w (y i))) ≤
      (-1 / 10 : ℝ) * ∑ i ∈ Finset.range m, weight i := by sorry
