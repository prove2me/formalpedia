-- Prove2me | solution 1 for e7_integral_eq_restrict_of_support_subset
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T07:44:23.184204+00:00
-- url     : https://prove2.me/submissions/6ee155c6-e6f9-457a-b193-ecf5c2d89541

import Mathlib

open MeasureTheory

theorem solution (f : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s)
    (hsupport : Function.support f ⊆ s) :
    (∫ x, f x ∂volume) = (∫ x, f x ∂(volume.restrict s)) := by
  symm
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    by_contra h
    exact hx (hsupport (Function.mem_support.mpr h)))
