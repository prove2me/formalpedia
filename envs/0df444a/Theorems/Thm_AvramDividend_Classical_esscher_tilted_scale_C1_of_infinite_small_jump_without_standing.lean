-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_C1_of_infinite_small_jump_without_standing
-- name    : AvramDividend.Classical.esscher_tilted_scale_C1_of_infinite_small_jump_without_standing
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T22:25:25.598987+00:00
-- url     : https://prove2.me/theorems/6344b1a4-8ee1-4f04-a20c-fdd8b5b96f0d
-- title:
--   Infinite small-jump variation smoothing of the Esscher-tilted scale function without standing assumptions
-- statement:
--   For a spectrally negative Lévy process with divergent first absolute small-negative-jump moment, the q-scale function and its Esscher tilt are continuously differentiable on the positive half-line. This isolates the non-Gaussian infinite-variation smoothing mechanism independently of integrable-positive-mean or standing assumptions. A proof requires regularity of the reflected process/excursion height law or a genuine analytic Wiener-Hopf potential-density argument; it cannot follow solely from Laplace-transform equality.
-- source:
--   Chan, Kyprianou and Savov (2011), Smoothness of scale functions for spectrally negative Lévy processes, unbounded-variation smoothness and excursion formulae; Kuznetsov, Kyprianou and Rivero (2012), theory of scale functions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_tilted_scale_C1_of_infinite_small_jump_without_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by sorry
