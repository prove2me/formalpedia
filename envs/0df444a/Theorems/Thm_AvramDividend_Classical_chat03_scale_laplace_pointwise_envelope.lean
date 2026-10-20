-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_scale_laplace_pointwise_envelope
-- name    : AvramDividend.Classical.chat03_scale_laplace_pointwise_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:49:13.85206+00:00
-- url     : https://prove2.me/theorems/e4ad6e3d-0cdc-4738-84f9-19b221b30a05
-- title:
--   Exponential q-scale envelope from the exact Laplace-transform characterisation
-- statement:
--   Let W be a published q-scale function for a spectrally negative Lévy process with the defining Laplace transform ∫_(0,∞)e^(-θz)W(z) dz = 1/(ψ(θ)-q) for θ≥0 and ψ(θ)>q. Because W is nonnegative and nondecreasing on nonnegative reserves, integrating over the unit interval (y,y+1] yields e^(-θ(y+1)) W(y) ≤ 1/(ψ(θ)-q) for every y≥0. This genuine analytic bound implies exponential growth control of W and is the source-faithful input for finite-horizon uniform integrability of stopped q-scale values. It requires no first-jump moment, right-continuous filtration or unjustified optional stopping.
-- source:
--   Chat 03, mathematical derivation 19 October 2026 from Avram, Palmowski and Pistorius, arXiv:math/0702893, Section 3.2 equation (3.4), and exact Formalpedia IsScaleFunction definition at pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_scale_laplace_pointwise_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (hy : 0 ≤ y) :
    Real.exp (-(θ * (y + 1))) * W y ≤ (X.ψ θ - q)⁻¹ := by sorry
