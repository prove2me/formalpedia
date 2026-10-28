-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_tilted_C1_transport_of_scale_C1
-- name    : AvramDividend.Classical.esscher_tilted_C1_transport_of_scale_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:40:33.530993+00:00
-- url     : https://prove2.me/theorems/1b84645e-79fd-4bbe-9782-cd9eb95c8d5a
-- title:
--   Esscher-tilted scale inherits C1 regularity from the untilted scale function
-- statement:
--   If the scale function W is C1 on the positive half-line and V agrees there with the Esscher-tilted product x ↦ exp(-φx) * W x, then V is C1 there by the product rule for C1 functions and smoothness of the exponential factor. This isolates the smoothness-transport step used by the unbounded-tilted C1 reductions for 0883e459, so the remaining obligation is exactly scale-function regularity under infinite small-jump variation.
-- source:
--   Product rule for continuously differentiable functions; smoothness of x ↦ Real.exp (-(φ * x)). Transport step extracted from the 0883e459 proof architecture (dichotomy + branch C1).

import Mathlib

open Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_tilted_C1_transport_of_scale_C1
    (W V : ℝ → ℝ) (φ : ℝ)
    (hW : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)))
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by sorry
