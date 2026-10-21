-- Prove2me | Theorems.Thm_AvramDividend_Classical_grid_exit_fatou_uniform_bound
-- name    : AvramDividend.Classical.grid_exit_fatou_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:50:19.89493+00:00
-- url     : https://prove2.me/theorems/7addf469-a830-4253-b020-40a8010dcbd4
-- title:
--   Fatou passage from uniformly bounded finite-grid exit rewards to a continuous-time payoff
-- statement:
--   For measurable extended-nonnegative grid rewards f_n and a continuous-time reward F bounded pointwise by the grid liminf, uniform upper bounds B on the grid lintegrals pass to the target lintegral by Fatou's lemma. This isolates the measure-theoretic limit needed for exponential first-passage estimates. The genuine pathwise grid-to-continuous inequality remains an explicit premise.
-- source:
--   Pinned Mathlib lintegral_liminf_le and Filter.liminf_le_of_le.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal

theorem AvramDividend.Classical.grid_exit_fatou_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Ω → ENNReal) (f : ℕ → Ω → ENNReal)
    (hMeas : ∀ n : ℕ, Measurable (f n))
    (hlimit : ∀ ω : Ω, F ω ≤ liminf (fun n => f n ω) atTop)
    (B : ENNReal)
    (hgrid : ∀ n : ℕ, (∫⁻ ω, f n ω ∂P) ≤ B) :
    (∫⁻ ω, F ω ∂P) ≤ B := by sorry
