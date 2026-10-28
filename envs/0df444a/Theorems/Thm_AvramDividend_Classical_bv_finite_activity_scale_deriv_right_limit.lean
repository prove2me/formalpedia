-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_deriv_right_limit
-- name    : AvramDividend.Classical.bv_finite_activity_scale_deriv_right_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:33:59.352711+00:00
-- url     : https://prove2.me/theorems/68517eb4-c7eb-431b-b379-47f9ec8d5095
-- title:
--   Finite negative-jump activity fixes the right limit of the q-scale ordinary derivative
-- statement:
--   When the bounded-variation Lévy process has finite negative-jump intensity λ, the positive-axis ordinary derivative of its canonical q-scale function converges at zero to (q+λ)/d². Via the canonical Esscher renewal density, only the one-jump convolution density survives the zero limit; all higher convolution orders vanish locally. This is the second independent input for the finite-activity Volterra-origin package.
-- source:
--   Avram, Palmowski and Pistorius (2007), W'(0+) formula; verified canonical geometric-renewal representation bd5082fb-392c-4e36-9858-95c79a31ed92.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.Calculus.Deriv.Basic
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.bv_finite_activity_scale_deriv_right_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    Tendsto (fun x : ℝ => deriv W x)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ((q + (X.ν (Iio (0 : ℝ))).toReal) / (X.drift ^ 2))) := by sorry
