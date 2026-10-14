-- Prove2me | Theorems.Thm_ContDiff_iterate_directional_mul
-- name    : ContDiff.iterate_directional_mul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T17:54:30.124994+00:00
-- url     : https://prove2.me/theorems/cf86276d-37f9-4f6c-9cbc-0ca601bdc847
-- title:
--   Higher product rule along a fixed direction
-- statement:
--   Let E be any real normed vector space, a a fixed vector, and f and g globally smooth real-valued functions on E. Write D_a h(x) = fderiv ℝ h x a. For every natural number k, the k-fold iterate of D_a applied to fg equals the sum, for j from 0 through k, of choose(k,j) times (D_a^(k-j) f)(D_a^j g), as an equality of functions. No completeness, finite-dimensionality, or nonzero-direction hypothesis is imposed. The case k=0 is included.
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

theorem ContDiff.iterate_directional_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) (k : ℕ) (f g : E → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    (fun u y => fderiv ℝ u y a)^[k] (fun x => f x * g x) = fun x =>
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        (((fun u y => fderiv ℝ u y a)^[k-j] f) x *
         ((fun u y => fderiv ℝ u y a)^[j] g) x) := by sorry
