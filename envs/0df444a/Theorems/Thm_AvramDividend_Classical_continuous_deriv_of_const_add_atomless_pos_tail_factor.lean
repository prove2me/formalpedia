-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuous_deriv_of_const_add_atomless_pos_tail_factor
-- name    : AvramDividend.Classical.continuous_deriv_of_const_add_atomless_pos_tail_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T14:53:51.45287+00:00
-- url     : https://prove2.me/theorems/33715dce-b0bb-4724-a8af-0dd77b418fe3
-- title:
--   Derivative continuity from an Esscher constant plus locally finite atomless positive tails
-- statement:
--   If W is continuous on (0,∞) and W'(x)=W(x)(phi+mu([x,∞))) there, where mu is atomless and each strictly positive upper tail is finite, then W' is continuous on (0,∞). No finiteness at zero or for negative thresholds is assumed. This is the deterministic q-scale excursion-height regularity bridge.
-- source:
--   Uses continuousOn_measureReal_Ici_of_pos_finite_noAtoms plus continuity of addition and multiplication.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.continuous_deriv_of_const_add_atomless_pos_tail_factor
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤)
    (φ : ℝ) (W : ℝ → ℝ)
    (hWcont : ContinuousOn W (Ioi 0))
    (hderiv : ∀ x : ℝ, 0 < x →
      deriv W x = W x * (φ + μ.real (Ici x))) :
    ContinuousOn (deriv W) (Ioi 0) := by sorry
