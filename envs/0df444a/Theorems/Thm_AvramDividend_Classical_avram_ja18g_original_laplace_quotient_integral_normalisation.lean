-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_laplace_quotient_integral_normalisation
-- name    : AvramDividend.Classical.avram_ja18g_original_laplace_quotient_integral_normalisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:29:53.144143+00:00
-- url     : https://prove2.me/theorems/47c68ccf-712c-4231-8ade-8197985198ba
-- title:
--   Original exponential moment quotient equals integral of pointwise quotient
-- statement:
--   On the original probability space, for θ>0 and any t≥0, the difference quotient of E[exp(θX_t)] at the normalisation E[1]=1 equals E[(exp(θX_t)-1)/θ]. Prove via original X compensated-exponential integrability, deterministic factor exp(tψθ), integrability of the constant function one, and integral linearity. No independent auxiliary process.
-- source:
--   J-A18 original Laplace dominated convergence normalisation child

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_laplace_quotient_integral_normalisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0)
    (θ : ℝ) (hθ : 0 < θ) :
    ((∫ ω, Real.exp (θ * X.X t ω) ∂P) - 1) / θ =
      ∫ ω, (Real.exp (θ * X.X t ω) - 1) / θ ∂P := by sorry
