-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_finite_tagged_nonlinear_jump_discount_tendsto
-- name    : AvramDividend.Classical.avram_p3_2_original_finite_tagged_nonlinear_jump_discount_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:39:45.996275+00:00
-- url     : https://prove2.me/theorems/bdbb4bc1-6d03-456e-afc9-c38be328af5b
-- title:
--   Original BV finite-tagged nonlinear marked-jump grid converges with true jump-time discount
-- statement:
--   For any fixed finite set of genuinely tagged negative jump cells, if the source physical-grid postpayment prestate and raw-J cell increment converge to each actual jump's predictable prestate and mark, and both physical frozen-grid and true jump-time discount factors converge to the same weight, then the entire nonlinear discounted jump-cell sum converges to the actual tagged Lévy jump sum. Only continuity of w at the tagged prestates and post-jump values is required, allowing large negative jumps to be handled separately from the compact Lipschitz small-jump envelope. The missing source proof must establish the real original X/D prestate and raw jump limits and separately address boundary states where w is discontinuous; this theorem does not assume those conclusions.
-- source:
--   Finite-source nonlinear jump limit step for original F2 tagged cell capture 11e630d3 and source stopped C1 chain 59bbb211; exact analytic finite-sum continuity consequence, no surrogate process.

import Mathlib

open Filter
open scoped BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_finite_tagged_nonlinear_jump_discount_tendsto
    (w : ℝ → ℝ) (n : ℕ)
    (z j e d : ℕ → Fin n → ℝ)
    (p a r : Fin n → ℝ)
    (hz : ∀ i, Tendsto (fun k => z k i) atTop (𝓝 (p i)))
    (hj : ∀ i, Tendsto (fun k => j k i) atTop (𝓝 (a i)))
    (he : ∀ i, Tendsto (fun k => e k i) atTop (𝓝 (r i)))
    (hd : ∀ i, Tendsto (fun k => d k i) atTop (𝓝 (r i)))
    (hwp : ∀ i, ContinuousAt w (p i))
    (hwpa : ∀ i, ContinuousAt w (p i - a i)) :
    Tendsto (fun k =>
      (∑ i : Fin n, e k i *
        (w (z k i - j k i) - w (z k i))) -
      (∑ i : Fin n, d k i *
        (w (p i - a i) - w (p i)))) atTop (𝓝 0) := by sorry
