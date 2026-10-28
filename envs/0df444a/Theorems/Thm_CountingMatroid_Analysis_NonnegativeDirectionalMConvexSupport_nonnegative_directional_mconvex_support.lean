-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_NonnegativeDirectionalMConvexSupport_nonnegative_directional_mconvex_support
-- name    : CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport.nonnegative_directional_mconvex_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:28:20.026978+00:00
-- url     : https://prove2.me/theorems/78d2bd3c-6e4a-4fe0-9f73-f94362b4b533
-- title:
--   Nonnegative directional derivatives preserve support exchange
-- statement:
--   Let $\sigma$ be finite, let $n\in\mathbb N$, and let $p\in\mathbb Q[x_s:s\in\sigma]$ be homogeneous of degree $n$ with nonnegative coefficients. Assume its support has the exchange property: whenever $x,y\in\operatorname{supp}(p)$ and $y_i<x_i$, there is $j$ with $x_j<y_j$ and $x-e_i+e_j\in\operatorname{supp}(p)$, where $e_i$ is a unit exponent. For every nonnegative rational direction $d$, put $q=D_dp$. Then $$x,y\in\operatorname{supp}(q),\ y_i<x_i\ \Longrightarrow\ \exists j:\ x_j<y_j,\ x-e_i+e_j\in\operatorname{supp}(q).$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/NonnegativeDirectionalMConvexSupport.lean#L57-L182

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

theorem CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport.nonnegative_directional_mconvex_support {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (n : ℕ) (hhom : p.IsHomogeneous n)
    (hp : ∀ m, 0 ≤ p.coeff m)
    (hex : ∀ x ∈ p.support, ∀ y ∈ p.support, ∀ i, y i < x i →
      ∃ j, x j < y j ∧
        x - Finsupp.single i 1 + Finsupp.single j 1 ∈ p.support)
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) :
    let q := ∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p
    ∀ x ∈ q.support, ∀ y ∈ q.support, ∀ i, y i < x i →
      ∃ j, x j < y j ∧
        x - Finsupp.single i 1 + Finsupp.single j 1 ∈ q.support := by sorry
