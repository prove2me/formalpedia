-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_conditional_atom_lipschitz
-- name    : AvramDividend.Classical.gaussian_double_tail_conditional_atom_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:29:15.220146+00:00
-- url     : https://prove2.me/theorems/27064b42-958b-4439-bd38-27fae278811b
-- title:
--   Time-Lipschitz bound for the conditional Gaussian double-tail atom
-- statement:
--   For positive times s and t, the Gaussian strict-order double-tail atom 1_{0<t<z}(z−t)e^{−φz} is Lipschitz in time with pointwise bound |t−s|e^{−φz}. This is a direct bridge from the positive-part Lipschitz lemma to the conditional kernel used by Gaussian Tonelli.
-- source:
--   Accepted gaussian_double_tail_atom_lipschitz_time and elementary max/interval order cases.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_double_tail_conditional_atom_lipschitz
    (φ z s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    |(if 0 < t ∧ t < z then (z - t) * Real.exp (-φ * z) else 0) -
      (if 0 < s ∧ s < z then (z - s) * Real.exp (-φ * z) else 0)| ≤
      |t - s| * Real.exp (-φ * z) := by sorry
