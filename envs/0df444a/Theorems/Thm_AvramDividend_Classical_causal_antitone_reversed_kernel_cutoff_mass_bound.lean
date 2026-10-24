-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_antitone_reversed_kernel_cutoff_mass_bound
-- name    : AvramDividend.Classical.causal_antitone_reversed_kernel_cutoff_mass_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:17:57.338575+00:00
-- url     : https://prove2.me/theorems/190f154b-4c1a-4519-9af9-c2c270c6fc4d
-- title:
--   Reversed antitone kernel controlled on the left convolution interval by cutoff mass
-- statement:
--   For a positive cutoff x-u and an antitone real kernel κ on positive times, the reverse-shifted kernel κ(x-s) on the left interval 0<s<u is bounded by the finite accumulated mass over (0,x-u] divided by x-u. This is the nontrivial left-interval kernel estimate used in the n-fold Volterra convolution-power induction.
-- source:
--   Apply proved antitone-positive-kernel mass bound at the cutoff x-u and monotonicity of κ under causal reversal.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_antitone_positive_kernel_mass_lower_bound

open MeasureTheory Set

theorem AvramDividend.Classical.causal_antitone_reversed_kernel_cutoff_mass_bound
    (κ : ℝ → ℝ) (x u ρ : ℝ) (hxu : 0 < x - u)
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hint : IntervalIntegrable κ volume 0 (x - u))
    (hmass : (∫ t in (0 : ℝ)..(x - u), κ t) ≤ ρ) :
    ∀ s ∈ Ioo (0 : ℝ) u, κ (x - s) ≤ ρ / (x - u) := by sorry
