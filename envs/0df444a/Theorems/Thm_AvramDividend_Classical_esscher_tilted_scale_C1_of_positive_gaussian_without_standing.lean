-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_C1_of_positive_gaussian_without_standing
-- name    : AvramDividend.Classical.esscher_tilted_scale_C1_of_positive_gaussian_without_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T22:25:28.066139+00:00
-- url     : https://prove2.me/theorems/d5b62f36-c53e-43ba-8962-6d4efe26aa31
-- title:
--   Gaussian smoothing of the Esscher-tilted scale function without first-moment standing assumptions
-- statement:
--   For a spectrally negative Lévy process with strictly positive Gaussian coefficient, the q-scale function and its Esscher tilt are continuously differentiable at every positive level. This isolates Gaussian smoothing independently of moment/standing assumptions. The mathematical proof requires Gaussian regularity of the killed resolvent or the reflected-excursion height law. The positive root is supplied as an argument; no global Esscher change-of-measure on an arbitrary probability space is postulated.
-- source:
--   Chan, Kyprianou and Savov (2011), Smoothness of scale functions for spectrally negative Lévy processes, Gaussian and unbounded-variation smoothness via excursion theory; Kyprianou, Kuznetsov and Rivero (2012), theory of scale functions, smoothness criteria.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_tilted_scale_C1_of_positive_gaussian_without_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by sorry
