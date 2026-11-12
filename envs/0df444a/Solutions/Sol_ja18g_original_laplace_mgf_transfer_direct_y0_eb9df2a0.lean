-- Prove2me | solution 1 for ja18g_original_laplace_mgf_transfer_direct_y0_eb9df2a0
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:55:16.116032+00:00
-- url     : https://prove2.me/submissions/18bf2edc-6f34-4ff2-baa7-bb5333f7a578

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
    : (let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0); let y : ℝ → ℝ := fun θ => (t : ℝ) * X.ψ θ; let g : ℝ → ℝ := fun θ => y θ / θ; Tendsto y l (nhds 0)) := by
    let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0)
    let y : ℝ → ℝ := fun θ => (t : ℝ) * X.ψ θ
    let g : ℝ → ℝ := fun θ => y θ / θ
    have hh : Tendsto (fun θ => θ * g θ) l (nhds 0) := by
      simpa using (hθ.mul hg)
    apply hh.congr'
    filter_upwards [hpos] with θ hθpos
    dsimp [y, g]
    field_simp [ne_of_gt hθpos]
end
