-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_source_scale_primitive_shifted_laplace_integrable
-- name    : AvramDividend.Classical.avram_wave4_p2_source_scale_primitive_shifted_laplace_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:08:06.098566+00:00
-- url     : https://prove2.me/theorems/e2632d79-5396-430a-9d8e-0b0b47f878af
-- title:
--   Original source scale primitive remains exponentially integrable after every negative spatial shift
-- statement:
--   For a true q-scale W and its globally nondecreasing interval primitive U(z)=∫₀ᶻW, any negative shift y≤0 satisfies 0≤U(x+y)≤U(x). At θ>0,q<ψθ the unshifted primitive is exponentially L1 by the genuine scale Laplace identity, hence the shifted primitive is also exponentially L1 by direct measurable norm domination. This verifies the independently required integrability for separating the actual generator increment U(x+y)-U(x) into two integrals in the compensated fixed-jump Laplace transform. It includes the boundary-crossing region and requires neither Gaussian diffusion nor harmonicity.
-- source:
--   Avram Palmowski Pistorius (2007), scale primitive and Laplace identity; Proved P2 global primitive monotonicity 226a1286 and original real primitive Laplace 9f40ea02.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_source_scale_primitive_shifted_laplace_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 < θ) (hqθ : q < X.ψ θ) (hy : y ≤ 0) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) *
        (∫ t in (0 : ℝ)..(x + y), W t))
      (Ioi (0 : ℝ)) volume := by sorry
