-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_exp_memLp_two
-- name    : AvramDividend.Classical.levy_bounded_stopping_increment_exp_memLp_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:48:07.204646+00:00
-- url     : https://prove2.me/theorems/2dd30102-ce97-458a-af3e-d0acf300a08a
-- title:
--   L² membership of post-stopping Lévy exponential increments
-- statement:
--   The positive exponential of a Lévy increment after any bounded stopping time is in L², for each nonnegative Laplace parameter and fixed forward horizon. This follows by applying the exact bounded-stopping Laplace identity at θ and 2θ and the Mathlib equivalence between L² membership and square-integrability of a real-valued function.
-- source:
--   Apply levy_bounded_stopping_increment_laplace at θ and 2θ, deduce integrability from their nonzero integral values, then use memLp_two_iff_integrable_sq.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_increment_exp_memLp_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    MemLp (fun ω => Real.exp
      (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) 2 P := by sorry
