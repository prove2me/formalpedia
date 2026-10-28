-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_NonnegativeDirectionalMConvexSupport_mem_directional_support_iff
-- name    : CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport.mem_directional_support_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:47:39.564328+00:00
-- url     : https://prove2.me/theorems/abdf33d2-a57b-4fe8-a969-60e091ba20be
-- title:
--   Support of a nonnegative directional derivative
-- statement:
--   Let $\sigma$ be finite, let $p\in\mathbb Q[x_s:s\in\sigma]$ have nonnegative coefficients, and let $d\in\mathbb Q^\sigma$ have nonnegative coordinates. Write $D_dp=\sum_sd_s\partial_sp$, and let $m\in\mathbb N^\sigma$ be an exponent vector. With $e_s$ the $s$th unit vector and support defined by nonzero coefficients, $$m\in\operatorname{supp}(D_dp)\quad\Longleftrightarrow\quad\exists s\in\sigma:\ d_s>0\ \text{and}\ m+e_s\in\operatorname{supp}(p).$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/NonnegativeDirectionalMConvexSupport.lean#L31-L55

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Positivity

namespace CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
end CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
set_option autoImplicit false

/-!
Support calculations for a nonnegative directional derivative. Its coefficients
are nonnegative, and its support consists precisely of exponents obtained by
removing a unit in a direction with positive weight. The exchange condition
is preserved by a finite exchange argument on these lifted exponents.
-/

namespace CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
end CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport

open scoped BigOperators

theorem CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport.mem_directional_support_iff {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (hp : ∀ m, 0 ≤ p.coeff m)
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) (m : σ →₀ ℕ) :
    m ∈ (∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p).support ↔
      ∃ s, 0 < d s ∧ m + Finsupp.single s 1 ∈ p.support := by sorry
