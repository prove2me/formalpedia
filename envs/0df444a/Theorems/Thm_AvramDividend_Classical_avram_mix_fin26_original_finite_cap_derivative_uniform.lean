-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_finite_cap_derivative_uniform
-- name    : AvramDividend.Classical.avram_mix_fin26_original_finite_cap_derivative_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:48:02.238611+00:00
-- url     : https://prove2.me/theorems/2fe0aa92-eab5-458a-9600-1541f0dfcf9c
-- title:
--   Finite mixed generator HJB and finite activity force a uniform interior first-derivative bound up to the cap
-- statement:
--   On a finite cap interval [u,C) with u>0, the original mixed generator HJB supersolution and finite negative-jump intensity imply w''≤β w'+ε using the proven negative-mark kernel bound. The C² interior regularity makes w' continuously differentiable on [u,C), and the already Proved ODE comparison bounds w' uniformly as the upper cap is approached. Explicit reward nonnegativity and upper-bound premises isolate the boundary step without silently assuming C² smoothness at the cap. This is a direct analytic prerequisite for the physical stopped Ito boundary passage.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_finite_jump_generator_lower
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_hjb_diff_comparison
import Theorems.Thm_AvramDividend_Classical_avram_gauss_finitec2_cap_ode_derivative_uniform
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin26_original_finite_cap_derivative_uniform
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (q jumpRate W u C β ε : ℝ)
    (hu : 0 < u) (huC : u < C) (hβ : 0 ≤ β) (hε : 0 ≤ ε)
    (hA : 0 < X.σ ^ 2 / 2)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hJumpRate : jumpRate = (X.ν (Iio (0 : ℝ))).toReal)
    (hQ : 0 ≤ q + jumpRate)
    (hSmooth : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hDeriv : ∀ y ∈ Ico u C, 0 ≤ deriv w y)
    (hReward : ∀ y ∈ Ico u C, ∀ t : ℝ, t ≤ y → 0 ≤ w t)
    (hUpper : ∀ y ∈ Ico u C, w y ≤ W)
    (hHJB : ∀ y ∈ Ico u C,
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hBeta : -X.c ≤ (X.σ ^ 2 / 2) * β)
    (hEps : (q + jumpRate) * W ≤ (X.σ ^ 2 / 2) * ε) :
    ∃ B : ℝ, ∀ y ∈ Ico u C, deriv w y ≤ B := by sorry
