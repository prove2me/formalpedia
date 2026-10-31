-- Prove2me | Theorems.Thm_DifferentialTopology_positive_ratio_of_cooriented_regular_defining_functions
-- name    : DifferentialTopology.positive_ratio_of_cooriented_regular_defining_functions
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T20:25:04.522775+00:00
-- url     : https://prove2.me/theorems/1fa205be-95aa-4fd5-b5bc-97cba4db4023
-- title:
--   Smooth positive ratio of cooriented regular defining functions
-- statement:
--   Let $u,v:\mathbb R^2\to\mathbb R$ be smooth. Suppose zero is a regular value of each function, their zero sets coincide, and they have the same sign away from that set:
--   $$u^{-1}(0)=v^{-1}(0),\qquad u(x)v(x)>0\quad\text{when }v(x)\ne0.$$
--   Then there is a unique smooth positive function $a:\mathbb R^2\to(0,\infty)$ such that
--   $$u=a\,v.$$
--   Thus the ordinary quotient $u/v$, initially defined off the common zero curve, extends smoothly and positively across it. The conclusion also covers an empty zero set.
--
--   This is a smooth division consequence of Hadamard's lemma and the inverse function theorem. In contact geometry it permits cooriented regular dividing functions to be normalized to a common normal coefficient without changing the corresponding contact plane field under positive rescaling.
-- source:
--   Smooth division corollary of Hadamard's lemma with parameters and the inverse function theorem: J. Milnor, Morse Theory (1963), printed p.5, Lemma 2.1, https://www.maths.ed.ac.uk/~v1ranick/papers/milnmors.pdf. The global positive-factor conclusion is the stated corollary, not the verbatim lemma. Used for invariant contact-form normalization in Etnyre, Convex Surfaces in Contact Geometry notes, printed pp.11–13, proof of Theorem 2.26.

import Mathlib
open scoped ContDiff

theorem DifferentialTopology.positive_ratio_of_cooriented_regular_defining_functions
    (u v : (ℝ × ℝ) → ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hregu : ∀ x, u x = 0 → fderiv ℝ u x ≠ 0)
    (hregv : ∀ x, v x = 0 → fderiv ℝ v x ≠ 0)
    (hzero : ∀ x, u x = 0 ↔ v x = 0)
    (hsign : ∀ x, v x ≠ 0 → 0 < u x*v x) :
    ∃! a : (ℝ × ℝ) → ℝ, ContDiff ℝ ∞ a ∧ (∀ x, 0 < a x) ∧ ∀ x, u x = a x*v x := by sorry
