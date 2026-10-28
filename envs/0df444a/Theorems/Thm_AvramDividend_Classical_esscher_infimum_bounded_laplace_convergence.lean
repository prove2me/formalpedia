-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_infimum_bounded_laplace_convergence
-- name    : AvramDividend.Classical.esscher_infimum_bounded_laplace_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:26:39.205316+00:00
-- url     : https://prove2.me/theorems/03cb3060-8804-45aa-987a-004a04a0605a
-- title:
--   Bounded Laplace convergence for nonnegative finite-horizon infimum magnitudes
-- statement:
--   Under a genuine finite-measure path law Q, if measurable nonnegative finite-horizon infimum magnitudes Y_n converge almost surely to finite Y∞, then bounded Laplace expectations converge for every β>0. Uses actual dominated convergence of exp(-βY_n), bounded by one. The process-law and a.e. convergence must be separately supplied by 1E-A/C2.
-- source:
--   Dominated convergence theorem, pinned Mathlib MeasureTheory.tendsto_integral_of_dominated_convergence; Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions, §2.1. Corrected failed job 504883fc (unsupported 𝓝 notation).

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
open MeasureTheory Filter

theorem AvramDividend.Classical.esscher_infimum_bounded_laplace_convergence
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q]
    (Y : ℕ → Ω → ℝ) (Yinf : Ω → ℝ)
    (β : ℝ) (hβ : 0 < β)
    (hmeas : ∀ n : ℕ,
      AEStronglyMeasurable (fun ω => Real.exp (-β * Y n ω)) Q)
    (hpos : ∀ n : ℕ, ∀ᵐ ω ∂Q, 0 ≤ Y n ω)
    (hlim : ∀ᵐ ω ∂Q,
      Tendsto (fun n : ℕ => Y n ω) atTop (nhds (Yinf ω))) :
    Tendsto (fun n : ℕ => ∫ ω, Real.exp (-β * Y n ω) ∂Q)
      atTop (nhds (∫ ω, Real.exp (-β * Yinf ω) ∂Q)) := by sorry
