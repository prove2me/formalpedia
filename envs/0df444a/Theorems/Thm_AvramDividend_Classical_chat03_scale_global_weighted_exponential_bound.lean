-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_scale_global_weighted_exponential_bound
-- name    : AvramDividend.Classical.chat03_scale_global_weighted_exponential_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:05:57.824484+00:00
-- url     : https://prove2.me/theorems/8c6ea1c8-5e9c-452e-b0b2-0bfa4bb1d0c2
-- title:
--   Global exponential Laplace envelope including overshoots below ruin
-- statement:
--   For a spectrally negative Lévy process and its official q-scale function W, for every real reserve y, nonnegative theta with psi(theta)>q, the exponential-weighted scale function exp(-theta(y+1))*W(y) is at most 1/(psi(theta)-q). When y≥0 this is the already Proved unit-interval Laplace envelope; when y<0, W(y)=0 by the official scale definition. This extension allows uniform-integrability arguments for stopped reserves even where a downward jump overshoots the ruin threshold. It requires no first-jump moment, continuous-time stopping theorem or new filtration assumptions.
-- source:
--   Avram Palmowski Pistorius (2007) arXiv:math/0702893 Section 3.2 scale transform and canonical Formalpedia scale definition. Exact previously Proved child AvramDividend.Classical.chat03_scale_laplace_pointwise_envelope, UUID e4ad6e3d-0cdc-4738-84f9-19b221b30a05, pinned revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_laplace_pointwise_envelope

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_scale_global_weighted_exponential_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) :
    Real.exp (-(θ * (y + 1))) * W y ≤ (X.ψ θ - q)⁻¹ := by sorry
