-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_secant_dct
-- name    : AvramDividend.Classical.avram_locmoll_band_secant_dct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:40:40.57753+00:00
-- url     : https://prove2.me/theorems/ed7c0dd7-159c-42bf-b6d5-c6719fd701f4
-- title:
--   Dominated convergence for the extended dividend secant integrand
-- statement:
--   Dominated convergence for the extended dividend secant integrand
-- source:
--   Physical Stieltjes integral route to 8b646752-f25d-4029-9771-dda1d287c7e1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_secant_dct
    (μ : Measure ℝ) (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (a b c : ℕ → ℝ → ℝ) (A B E : ℝ → ℝ) (K : ℝ)
    (horder : ∀ᵐ t ∂μ, B t ≤ A t ∧ ∀ n, b n t ≤ a n t)
    (hends : ∀ᵐ t ∂μ, Tendsto (fun n => a n t) atTop (𝓝 (A t)) ∧
      Tendsto (fun n => b n t) atTop (𝓝 (B t)) ∧
      Tendsto (fun n => c n t) atTop (𝓝 (E t))) :
    let Q : ℝ → ℝ → ℝ := fun a b => if a = b then deriv g a else (g a - g b) / (a - b)
    let F : ℕ → ℝ → ℝ := fun n t => E t - c n t * Q (a n t) (b n t)
    let L : ℝ → ℝ := fun t => E t * (1 - Q (A t) (B t))
    (∀ n, AEStronglyMeasurable (F n) μ) →
    Integrable (fun _ : ℝ => K) μ →
    (∀ n, ∀ᵐ t ∂μ, ‖F n t‖ ≤ K) →
    Tendsto (fun n => ∫ t, F n t ∂μ) atTop (𝓝 (∫ t, L t ∂μ)) := by sorry
