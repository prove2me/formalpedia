-- Prove2me | solution 1 for siegel_symmetrized_cdf_unimodal_from_density_sign
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T18:10:30.63156+00:00
-- url     : https://prove2.me/submissions/a5b197ba-11cf-4807-9749-eea696a2cdaa

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false

open Set

theorem solution
    (F f : ℝ → ℝ) (μ c : ℝ)
    (hF : ∀ x, HasDerivAt F (f x) x)
    (hgL : ∀ x ∈ Set.Icc (0:ℝ) c, f x - f (2 * μ - x) ≤ 0)
    (hgR : ∀ x ∈ Set.Icc c μ, 0 ≤ f x - f (2 * μ - x)) :
    AntitoneOn (fun x => (F x + F (2 * μ - x)) / 2) (Set.Icc 0 c)
      ∧ MonotoneOn (fun x => (F x + F (2 * μ - x)) / 2) (Set.Icc c μ) := by
  have hFhat : ∀ x : ℝ,
      HasDerivAt (fun y => (F y + F (2 * μ - y)) / 2) ((f x - f (2 * μ - x)) / 2) x := by
    intro x
    have hinner : HasDerivAt (fun y : ℝ => 2 * μ - y) (-1) x :=
      (hasDerivAt_id x).const_sub (2 * μ)
    have hcomp : HasDerivAt (fun y : ℝ => F (2 * μ - y)) (f (2 * μ - x) * (-1)) x :=
      (hF (2 * μ - x)).comp x hinner
    have hsum : HasDerivAt (fun y : ℝ => F y + F (2 * μ - y))
        (f x + f (2 * μ - x) * (-1)) x := (hF x).add hcomp
    have := hsum.div_const 2
    exact this.congr_deriv (by ring)
  refine ⟨?_, ?_⟩
  · apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 c)
    · intro x _; exact ((hFhat x).continuousAt).continuousWithinAt
    · intro x _; exact (hFhat x).hasDerivWithinAt
    · intro x hx
      have hxIcc : x ∈ Set.Icc (0:ℝ) c := interior_subset hx
      have := hgL x hxIcc
      linarith
  · apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc c μ)
    · intro x _; exact ((hFhat x).continuousAt).continuousWithinAt
    · intro x _; exact (hFhat x).hasDerivWithinAt
    · intro x hx
      have hxIcc : x ∈ Set.Icc c μ := interior_subset hx
      have := hgR x hxIcc
      linarith
