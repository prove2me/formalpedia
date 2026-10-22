-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_scale_shift_weighted_abs_integral_le_min
-- name    : AvramDividend.Classical.chat07_scale_shift_weighted_abs_integral_le_min
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:08:07.751994+00:00
-- url     : https://prove2.me/theorems/022bfe60-9e46-4abc-a8a7-5dbde7577d68
-- title:
--   First-order weighted scale shift bound uniform in jump magnitude
-- statement:
--   For a monotone q-scale function, exponentially weighted absolute negative-jump displacement is bounded by min(1,theta*r)/(psi(theta)-q). Combine the accepted exact weighted shift formula with the global exponential inequalities 1-exp(-t)<=min(1,t). The small-jump bound is first order in r and the large-jump bound is uniform, matching the bounded-variation Levy first-moment integrability requirement. No differentiability or absolute continuity is required.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_scale_shift_weighted_abs_integral_le_min
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (r : ℝ) (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) * |W x - W (x - r)|) ≤
      min 1 (θ * r) * (X.ψ θ - q)⁻¹ := by sorry
