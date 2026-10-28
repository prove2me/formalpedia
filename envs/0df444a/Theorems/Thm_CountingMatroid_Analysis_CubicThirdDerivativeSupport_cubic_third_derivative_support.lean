-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_CubicThirdDerivativeSupport_cubic_third_derivative_support
-- name    : CountingMatroid.Analysis.CubicThirdDerivativeSupport.cubic_third_derivative_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:47:35.422188+00:00
-- url     : https://prove2.me/theorems/e75ba2e8-6baf-45ca-9ad1-382db9f5319c
-- title:
--   Cubic support is detected by third derivatives
-- statement:
--   Let $\sigma$ be a variable type with decidable equality and let $p\in\mathbb Q[z_s:s\in\sigma]$ be homogeneous of degree three. For any finitely supported exponent vector $m:\sigma\to\mathbb N$,
--
--   $$m\in\operatorname{supp}(p)\iff
--   \exists s,i,j:\ \operatorname{ct}(\partial_i\partial_j\partial_s p)\ne0
--   \ \land\ m=e_i+e_j+e_s.$$
--
--   Here $\operatorname{ct}$ denotes constant coefficient and $e_i$ is a unit exponent vector. Indices may repeat. No coefficient-sign or finite-variable hypothesis is needed.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/CubicThirdDerivativeSupport.lean#L33-L59

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Count
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Positivity

namespace CountingMatroid.Analysis.CubicThirdDerivativeSupport
end CountingMatroid.Analysis.CubicThirdDerivativeSupport
set_option autoImplicit false

/-!
The nonzero entries of the third-derivative tensor of a homogeneous cubic
record exactly its monomial support, including repeated indices. This is a
polynomial-calculus bridge; it asserts no spectral closure property.
-/

namespace CountingMatroid.Analysis.CubicThirdDerivativeSupport
end CountingMatroid.Analysis.CubicThirdDerivativeSupport
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CubicThirdDerivativeSupport

theorem CountingMatroid.Analysis.CubicThirdDerivativeSupport.cubic_third_derivative_support {σ : Type} [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (hhom : p.IsHomogeneous 3) (m : σ →₀ ℕ) :
    m ∈ p.support ↔ ∃ s i j,
      MvPolynomial.constantCoeff (MvPolynomial.pderiv i
        (MvPolynomial.pderiv j (MvPolynomial.pderiv s p))) ≠ 0 ∧
      m = Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single s 1 := by sorry
