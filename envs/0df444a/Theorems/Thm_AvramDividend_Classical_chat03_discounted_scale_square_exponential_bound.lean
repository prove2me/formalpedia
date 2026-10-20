-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_discounted_scale_square_exponential_bound
-- name    : AvramDividend.Classical.chat03_discounted_scale_square_exponential_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:10:06.579664+00:00
-- url     : https://prove2.me/theorems/4ed6475b-52de-4e4a-b180-9a9b9032ca13
-- title:
--   Pointwise squared exponential growth domination of discounted q-scale payoffs
-- statement:
--   For an official q-scale function W of a spectrally negative Lévy process, q≥0, θ≥0 with ψ(θ)>q, any real reserve y (including an overshoot below zero), and any nonnegative time t, the squared discounted scale value [e^(-qt)W(y)]² is bounded above by [e^(θ(y+1))/(ψ(θ)-q)]². This is the exact pointwise square domination needed to control finite-horizon stopped q-scale payoffs by exponentially tilted Lévy moments. It follows directly from the accepted one-sided Laplace envelope, the zero extension W(y)=0 below zero, positivity, and e^(-qt)≤1. No optional-stopping theorem or continuous-time filtration regularity is required.
-- source:
--   Avram Palmowski Pistorius (2007), arXiv:math/0702893, Section 3.2, scale Laplace transform; Proved chat03_scale_laplace_pointwise_envelope e4ad6e3d-0cdc-4738-84f9-19b221b30a05, pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_laplace_pointwise_envelope
import Mathlib.Tactic.Linarith

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_discounted_scale_square_exponential_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (t : ℝ≥0) :
    (Real.exp (-(q * (t : ℝ))) * W y) ^ 2 ≤
      (Real.exp (θ * (y + 1)) * (X.ψ θ - q)⁻¹) ^ 2 := by sorry
