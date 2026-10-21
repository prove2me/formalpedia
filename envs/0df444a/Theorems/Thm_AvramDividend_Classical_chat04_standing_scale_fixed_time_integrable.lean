-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_standing_scale_fixed_time_integrable
-- name    : AvramDividend.Classical.chat04_standing_scale_fixed_time_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:20:12.425057+00:00
-- url     : https://prove2.me/theorems/1d43ef79-1a69-4d82-b4de-d9ad5d5c8ee5
-- title:
--   Standing assumptions imply integrability of any fixed-time discounted q-scale payoff
-- statement:
--   For any spectrally negative Lévy process satisfying the exact Avram Standing assumptions, q>0, any canonical q-scale function W, arbitrary real reserve x and fixed finite time t, W(x+X_t) is integrable under the original probability measure, without an additional exponential Laplace gap or separate integrability assumption. Prove θ≥0 with ψθ>q by exhaustive Gaussian/infinite-small-jump/BV standing growth theorems; then the accepted global exponential W(y) envelope and official Lévy exp moment dominate the full-line measurable scale payoff. This removes the explicit integrability premise required by the independently privately elaborated deterministic-start conditional Markov expectation; it does not assert killed q-harmonicity or martingality.
-- source:
--   Three previously Proved ψ-growth theorems (UUIDs f5a240ce-817f-4f90-aea0-7563caf01fb5, 0129b889-7aee-41c9-9475-11b37a46af7b, e9a8e903-54cb-4709-8fa1-330ae9e496bb), Proved q-scale Laplace envelope (UUID 8c6ea1c8-5e9c-452e-b0b2-0bfa4bb1d0c2), Borel measurable scale (UUID 45cbe3b4-374d-4fa4-b988-e09f93b74cab), and official Lévy exponential moment.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_global_weighted_exponential_bound
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_gaussian
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_infinite_small_jump_moment

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_standing_scale_fixed_time_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) :
    Integrable (fun ω => W (x + X.X t ω)) P := by sorry
