-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_nonnegative_kernel_envelope_antitone
-- name    : AvramDividend.Classical.causal_weighted_nonnegative_kernel_envelope_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:34:50.215834+00:00
-- url     : https://prove2.me/theorems/c537098d-c426-4fb3-ab06-b42b9a24fb27
-- title:
--   Damped nonnegative envelope of a decreasing causal kernel remains decreasing
-- statement:
--   For a nonnegative antitone causal kernel and a nonnegative exponential damping rate, the envelope obtained by adding the absolute value of a signed drift parameter and damping remains antitone on positive times. This supplies the monotone positive majorant used to estimate signed Volterra convolution powers.
-- source:
--   Gaussian scale-function C2 regularity: monotone nonnegative majorant of the signed weighted derivative-resolvent kernel.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Monotone.Defs
import Mathlib.Tactic.Linarith

open Set

theorem AvramDividend.Classical.causal_weighted_nonnegative_kernel_envelope_antitone
    (K : ℝ → ℝ) (w β : ℝ) (hw : 0 ≤ w)
    (hanti : AntitoneOn K (Ioi (0 : ℝ)))
    (hK0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ K t) :
    AntitoneOn (fun t : ℝ => Real.exp (-w * t) * (|β| + K t))
      (Ioi (0 : ℝ)) := by sorry
