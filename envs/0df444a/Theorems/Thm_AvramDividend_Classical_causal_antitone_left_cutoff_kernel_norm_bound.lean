-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_antitone_left_cutoff_kernel_norm_bound
-- name    : AvramDividend.Classical.causal_antitone_left_cutoff_kernel_norm_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:49:32.817067+00:00
-- url     : https://prove2.me/theorems/ccde1835-38eb-435b-aea2-f0c31551e983
-- title:
--   Antitone reversed causal kernel has a finite left-cutoff norm bound
-- statement:
--   For a nonnegative positive-time antitone kernel, its reflected translate κ(x-s) is uniformly norm-bounded by κ(x-u) on the left causal split 0<s≤u<x. This supplies the missing left essential-bound hypothesis for the two-piece convolution-integrability lemma, even when the kernel is unbounded near zero.
-- source:
--   Antitonicity between x-u and x-s, positivity of the reflected times, and equality of the real norm with absolute value.

import Mathlib.Analysis.Convolution
import Mathlib.Tactic.Linarith

open MeasureTheory Set

theorem AvramDividend.Classical.causal_antitone_left_cutoff_kernel_norm_bound
    (κ : ℝ → ℝ) (x u s : ℝ)
    (hu : 0 < u) (hux : u < x)
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hKnonneg : ∀ t : ℝ, 0 < t → 0 ≤ κ t)
    (hs : s ∈ Ioc (0 : ℝ) u) :
    ‖κ (x - s)‖ ≤ κ (x - u) := by sorry
