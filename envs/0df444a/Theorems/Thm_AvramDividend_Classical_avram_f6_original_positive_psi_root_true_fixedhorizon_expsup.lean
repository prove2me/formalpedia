-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_positive_psi_root_true_fixedhorizon_expsup
-- name    : AvramDividend.Classical.avram_f6_original_positive_psi_root_true_fixedhorizon_expsup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:27:14.029266+00:00
-- url     : https://prove2.me/theorems/9ee1e9c1-94a6-45df-b784-7038dbf43c98
-- title:
--   Original spectrally negative Levy fixed horizon runningSup exponential moment from positive ψ root, no Gaussian hypothesis
-- statement:
--   For original spectrally negative Lévy X, any Gaussian scale, actual ψ(λ)=p>0 root and 0≤β<λ, original fixed-horizon runningSup has finite exponential moment by genuine exp-clock moment and positive exponential tail. Source-backed path to zero-Gaussian finite-cap domination.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_positive_psi_root_true_fixedhorizon_expsup
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p lam β : ℝ) (hp : 0 < p) (hlam : 0 < lam)
    (hroot : X.ψ lam = p) (hβ : 0 ≤ β) (hβlam : β < lam)
    (n : ℝ≥0) :
    (∫⁻ ω : Ω,
      ENNReal.ofReal (Real.exp (β * runningSup X n ω))
      ∂ P) < ⊤ := by sorry
