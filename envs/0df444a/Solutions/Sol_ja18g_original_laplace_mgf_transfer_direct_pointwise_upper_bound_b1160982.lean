-- Prove2me | solution 1 for ja18g_original_laplace_mgf_transfer_direct_pointwise_upper_bound_b1160982
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:55:20.161393+00:00
-- url     : https://prove2.me/submissions/ed4b35ba-f5c4-4194-a29c-41ead9a244d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_eigenfunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0)
    (a : ℝ)
    (hψ : Filter.Tendsto (fun θ : ℝ => X.ψ θ / θ)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds a)) 
    (hθ : (let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0); let y : ℝ → ℝ := fun θ => (t : ℝ) * X.ψ θ; let g : ℝ → ℝ := fun θ => y θ / θ; Tendsto (fun θ : ℝ => θ) l (nhds 0)))
    (hg : (let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0); let y : ℝ → ℝ := fun θ => (t : ℝ) * X.ψ θ; let g : ℝ → ℝ := fun θ => y θ / θ; Tendsto g l (nhds ((t : ℝ) * a))))
    (hpos : (let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0); let y : ℝ → ℝ := fun θ => (t : ℝ) * X.ψ θ; let g : ℝ → ℝ := fun θ => y θ / θ; ∀ᶠ θ in l, 0 < θ))
    (hy0 : (let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0); let y : ℝ → ℝ := fun θ => (t : ℝ) * X.ψ θ; let g : ℝ → ℝ := fun θ => y θ / θ; Tendsto y l (nhds 0)))
    : (let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0); let y : ℝ → ℝ := fun θ => (t : ℝ) * X.ψ θ; let g : ℝ → ℝ := fun θ => y θ / θ; ∀ᶠ θ in l, |y θ| ≤ 1) := by
    let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0)
    let y : ℝ → ℝ := fun θ => (t : ℝ) * X.ψ θ
    let g : ℝ → ℝ := fun θ => y θ / θ
    have hh : Ioo (-1 : ℝ) 1 ∈ nhds (0 : ℝ) :=
      Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [hy0.eventually hh] with θ hθsmall
    exact abs_le.mpr ⟨hθsmall.1.le, hθsmall.2.le⟩
end
