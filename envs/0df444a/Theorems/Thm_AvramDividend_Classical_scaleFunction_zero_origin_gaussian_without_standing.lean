-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
-- name    : AvramDividend.Classical.scaleFunction_zero_origin_gaussian_without_standing
-- status  : Open
-- author  : @WillR
-- created : 2026-10-19T22:27:36.347385+00:00
-- url     : https://prove2.me/theorems/20b1acb4-bfe6-483b-bceb-2f0bbd6b6842
-- title:
--   Positive Gaussian coefficient forces the canonical q-scale function to vanish at the origin without Standing
-- statement:
--   For a spectrally negative Lévy process with positive Gaussian coefficient, any canonical q-scale function for q>0 vanishes at zero, without Standing or finite first moment. Use the proved quadratic lower bound ψ(θ)≥cθ+(σ²/2)θ²−ν((−∞,−1]) and positivity of σ to dominate linear terms above an explicit threshold, then invoke the Laplace-origin zero criterion.
-- source:
--   Lévy–Khintchine quadratic coercivity, Laplace transform of the scale function, and the origin-zero Tauberian bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_zero_origin_gaussian_without_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) : W 0 = 0 := by sorry
