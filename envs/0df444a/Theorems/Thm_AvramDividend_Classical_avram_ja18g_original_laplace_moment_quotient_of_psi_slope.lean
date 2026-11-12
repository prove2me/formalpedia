-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_laplace_moment_quotient_of_psi_slope
-- name    : AvramDividend.Classical.avram_ja18g_original_laplace_moment_quotient_of_psi_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:38:34.592419+00:00
-- url     : https://prove2.me/theorems/1fe8276d-433d-413d-aff7-1edf36d265e4
-- title:
--   Original Laplace moment quotient inherits the Lévy exponent first derivative
-- statement:
--   If the original ψ(θ)/θ has a finite right limit a, then the original moment quotient (E[e^{θX_t}]-1)/θ tends to t*a. Use the original spectrally negative Lévy Laplace transform identity E[e^{θX_t}]=exp(tψ(θ)) and scalar exp derivative at zero. This is the analytic transfer and introduces no additional random process.
-- source:
--   J-A18 original-process mgf transfer step

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_laplace_moment_quotient_of_psi_slope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0)
    (a : ℝ)
    (hψ : Filter.Tendsto (fun θ : ℝ => X.ψ θ / θ)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds a)) :
    Filter.Tendsto
      (fun θ : ℝ =>
        ((∫ ω, Real.exp (θ * X.X t ω) ∂P) - 1) / θ)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds ((t : ℝ) * a)) := by sorry
