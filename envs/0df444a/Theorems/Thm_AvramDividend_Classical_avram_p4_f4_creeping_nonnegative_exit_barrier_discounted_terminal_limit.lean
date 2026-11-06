-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_creeping_nonnegative_exit_barrier_discounted_terminal_limit
-- name    : AvramDividend.Classical.avram_p4_f4_creeping_nonnegative_exit_barrier_discounted_terminal_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:05:29.419883+00:00
-- url     : https://prove2.me/theorems/3b212fb1-4a49-49d4-8745-0cf85da361ca
-- title:
--   Shrinking nonnegative original exit barrier forces discounted creeping terminal value convergence
-- statement:
--   A deterministic shrinking positive interior exit barrier 0≤reserve_k≤barrier_k→0 and convergent stopping clock jointly force discounted value w(reserve_k) to converge to discounted w(0), assuming only canonical continuity on the nonnegative half-line. This isolates the exact creeping-ruin terminal convergence step; identifying physical original stopped reserve bounds and clocks remains a separate obligation.
-- source:
--   Squeeze original-style nonnegative exit reserve values between zero and a barrier tending to zero. Use ContinuousOn w (Ici 0) and continuous discount factor. This removes any assumed reserve Tendsto from the prior conditional creeping formulation, relying only on exit-band inequalities directly amenable to a physical localiser.

import Mathlib

open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_creeping_nonnegative_exit_barrier_discounted_terminal_limit
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (q t : ℝ) (clock reserve barrier : ℕ → ℝ)
    (hclock : Tendsto clock atTop (𝓝 t))
    (hbarrier : Tendsto barrier atTop (𝓝 (0 : ℝ)))
    (hreserveNN : ∀ k, 0 ≤ reserve k)
    (hreserveLe : ∀ k, reserve k ≤ barrier k) :
    Tendsto
      (fun k => Real.exp (-(q * clock k)) * w (reserve k))
      atTop (𝓝 (Real.exp (-(q * t)) * w 0)) := by sorry
