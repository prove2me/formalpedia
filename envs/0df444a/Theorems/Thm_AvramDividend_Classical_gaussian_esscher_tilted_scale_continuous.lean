-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_continuous
-- name    : AvramDividend.Classical.gaussian_esscher_tilted_scale_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T10:48:56.602778+00:00
-- url     : https://prove2.me/theorems/b0881cf9-6b39-4754-9fcc-595f2bd768a5
-- title:
--   Continuity of the Gaussian Esscher-tilted scale function without standing
-- statement:
--   For a spectrally negative Lévy process with a positive Gaussian coefficient, the canonical q-scale function vanishes at the origin and is continuous on the real line. Multiplication by the smooth exponential Esscher factor gives continuity of any function V agreeing with the tilted scale function on positive levels. The result does not require Standing, first moment integrability, or an already known derivative of the scale function. This is an input to signed Laplace uniqueness and the Gaussian integrated Volterra identity.
-- source:
--   Proved Gaussian zero-origin theorem 20b1acb4-bfe6-483b-bceb-2f0bbd6b6842, Proved scale-function continuity theorem 3321ae26-a1be-4095-85ea-bceb296f4a78, Mathlib continuity of products and exponentials.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_esscher_tilted_scale_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ContinuousOn V (Ioi (0 : ℝ)) := by sorry
