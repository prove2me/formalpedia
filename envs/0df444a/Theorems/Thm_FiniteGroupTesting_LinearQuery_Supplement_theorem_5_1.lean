-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_Supplement_theorem_5_1
-- name    : FiniteGroupTesting.LinearQuery.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:25:30.035096+00:00
-- url     : https://prove2.me/theorems/e4dce32e-43e3-4764-b96b-c93e19cf79a9
-- title:
--   Theorem 5.1 — Two-sided sublinear-query companion theorem
-- statement:
--   There is a positive absolute constant $C$, fixed before every size, accuracy and input, such that for all $n\ge2$ and $0<\epsilon<1/2$ the Section 5 program is a two-sided $\epsilon$-tester and every run uses at most
--   $$C\left(\sqrt{n/\bar\epsilon}\,(\log n)^{3/2}\sqrt{\log(1/\bar\epsilon)}+\frac{(\log n)^3}{\bar\epsilon}\right)$$
--   queries, where $\bar\epsilon=\max(\epsilon,n^{-2})$. The same uniform $C$ can also bound its queries by
--   $$C\left(\sqrt{n/\epsilon}+1/\epsilon\right)\left(\log n+\log(1/\epsilon)\right)^3.$$
--   For every fixed $\epsilon\in(0,1/2)$ there is $C_\epsilon>0$ such that every $n\ge2$ has query bound $C_\epsilon\sqrt n(\log n)^3$. Thus every displayed clause of the printed bound, including the fixed-accuracy consequence, is retained. Computation between queries is unrestricted.
--
--   In the nonfallback branch the bound also records $2k\lceil\log_2n\rceil+m+R_{\rm act}(2+2L)+R_{\rm prod}(1+3L)$. The constants $c_D,n_0,\gamma,C_L,C_A,C_P$ and the expansion/fallback choices are fixed as in the program definition. The ceiling choice of $m$ is a permitted uniform instantiation of the source's $\Theta$ formula; all trial counts are ceilings. The logarithm is natural, and $\log n\le\log(2n)\le2\log n$ for $n\ge2$. No lower bound $\epsilon\ge n^{-2}$ is assumed.
--
--   Differences from the source:
--   - encoding: labels [n]={1,...,n} → Fin n with zero representing paper label 1; reason: bijective relabelling preserves all tables, distances and query policies
--   - encoding: sufficient absolute constants in Sections 4–5 → fixed c_D=1/500, n_0=1500, gamma=1/10000, C_L=100, C_A=2000000, C_P=1000 and globally chosen expansion/fallback parameters; reason: these instantiate the displayed proof estimates uniformly; the predicates selecting numeric constants assume no existence or correctness, and the existing base theorems supply their witnesses
--   - encoding: candidate filters and possible early offline rejection before later trials → offline conjunction checked at the final decision, after shared action and product records are sampled; reason: this preserves every acceptance probability and the stated worst-case budget; it accesses the input only through the same visible oracle queries
--   - encoding: the Theta choice of m and soft-O notation → the ceiling square-root formula for m and a uniform logarithmic exponent 3, alongside the exact detailed bound; reason: these instantiate the displayed proof formulas without changing their order or domain; the fixed-epsilon constant alone may depend on epsilon
--   - generalization: there is a randomized adaptive two-sided tester with the stated query complexity → the specific Section 5 program sublinearTester has these bounds, and additionally its exact non-fallback query count 2k ceil(log_2 n) + m + R_act(2+2L) + R_prod(1+3L) when n >= 1500 and m <= n/500; reason: this is the tester assembled in Section 5.5 with the query accounting of (8.23); taking it as the witness gives the existential statement of the source
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 29, Theorem 5.1

import Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_UpperTester

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery.Supplement

theorem theorem_5_1 :
    ∃ C : ℝ, 0 < C ∧
      (∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1/2 →
        TwoSided ε (sublinearTester n ε) ∧
        QueryBound (sublinearTester n ε) (C * detailedBound n ε) ∧
        QueryBound (sublinearTester n ε) (C * softBound 3 n ε) ∧
        (1500 ≤ n → (dictionarySize n ε : ℝ) ≤ (n : ℝ) / 500 →
          QueryBound (sublinearTester n ε) (nonfallbackBudget n ε))) ∧
      (∀ ε : ℝ, 0 < ε → ε < 1/2 → ∃ Cε : ℝ, 0 < Cε ∧
        ∀ n : ℕ, 2 ≤ n → QueryBound (sublinearTester n ε)
          (Cε * Real.sqrt n * (Real.log n) ^ 3)) := by sorry

end FiniteGroupTesting.LinearQuery.Supplement
