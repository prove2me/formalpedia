-- Prove2me | Theorems.Thm_ContDiff_ordered_directional_mul
-- name    : ContDiff.ordered_directional_mul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T17:56:46.191933+00:00
-- url     : https://prove2.me/theorems/648e95b8-f7be-405d-ae03-47b0dafc9634
-- title:
--   Higher product rule for an ordered family of directions
-- statement:
--   Let E be a real normed vector space, let a be an ordered family of m constant vectors, and let beta assign a natural derivative order to each vector. For globally smooth real functions f and g, compose the beta_i-fold directional derivatives in increasing coordinate order using the indicated right fold. At every x, the result on fg is the sum over all gamma coordinatewise at most beta of the product of the coordinate binomial coefficients times the ordered beta-minus-gamma derivative of f and the ordered gamma derivative of g. The directions may repeat or vanish, and need not be a basis. Zero orders and the empty family are included. No completeness or finite-dimensionality hypothesis is required.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, section 1.8 (printed p. 10) and Proposition 3.16 proof (printed p. 54). Derived higher classical product formula; the real normed-space constant-direction formulation is a generalization, not a verbatim statement.

import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Pi.Interval
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

open scoped ContDiff
set_option autoImplicit false

theorem ContDiff.ordered_directional_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (a : Fin m → E) (β : Fin m → ℕ)
    (f g : E → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) :
    (List.finRange m).foldr
      (fun i h => (fun u y => fderiv ℝ u y (a i))^[β i] h) (fun y => f y * g y) x =
    ∑ γ ∈ Finset.Iic β, (∏ i, (Nat.choose (β i) (γ i) : ℝ)) *
      ((List.finRange m).foldr
        (fun i h => (fun u y => fderiv ℝ u y (a i))^[β i - γ i] h) f x *
       (List.finRange m).foldr
        (fun i h => (fun u y => fderiv ℝ u y (a i))^[γ i] h) g x) := by sorry
