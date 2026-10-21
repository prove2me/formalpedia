-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuous_upperfirst_bound_from_grid
-- name    : AvramDividend.Classical.continuous_upperfirst_bound_from_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T20:07:42.637111+00:00
-- url     : https://prove2.me/theorems/700d2ba2-8231-46ef-9f2f-a264674ba11e
-- title:
--   Continuous two-sided upper-first discounted exit bound from finite-grid clock convergence
-- statement:
--   Let upper and lower strict first-passage clocks be extended nonnegative random times with convergent grid approximations. If there is strict clock ordering or both are infinite on every path, then a uniform upper bound on the integrals of measurable upper-first grid-discount rewards passes to the integral of the true upper-first reward. On ordered paths, the accepted upper-first/lower-first grid convergence result identifies the liminf; on both-infinite paths the limiting reward vanishes. Fatou's lemma transports the integral bound. This isolates precisely the remaining stochastic clock convergence and no-simultaneous-finite-exit obligations.
-- source:
--   Proved grid_upperfirst_liminf_of_strict_order and grid_exit_fatou_uniform_bound.

import Mathlib
open MeasureTheory Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.continuous_upperfirst_bound_from_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (q : ℝ)
    (up down : Ω → ENNReal)
    (upGrid downGrid : ℕ → Ω → ENNReal)
    (hu : ∀ ω, Tendsto (fun n => upGrid n ω) atTop (nhds (up ω)))
    (hd : ∀ ω, Tendsto (fun n => downGrid n ω) atTop (nhds (down ω)))
    (hSep : ∀ ω, up ω < down ω ∨ down ω < up ω ∨
      (up ω = ⊤ ∧ down ω = ⊤))
    (hMeas : ∀ n : ℕ, Measurable
      (fun ω => if upGrid n ω < downGrid n ω then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (upGrid n ω))))
        else 0))
    (B : ENNReal)
    (hGrid : ∀ n : ℕ,
      (∫⁻ ω, (if upGrid n ω < downGrid n ω then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (upGrid n ω))))
        else 0) ∂P) ≤ B) :
    (∫⁻ ω, (if up ω < down ω then
      ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (up ω))))
      else 0) ∂P) ≤ B := by sorry
