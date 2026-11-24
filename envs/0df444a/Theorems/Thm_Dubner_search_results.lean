-- Prove2me | Theorems.Thm_Dubner_search_results
-- name    : Dubner.search_results
-- status  : Open
-- author  : @Idealson
-- created : 2026-11-24T11:32:13.81222+00:00
-- url     : https://prove2.me/theorems/d4cd27ce-ca17-4226-8599-f975612b8cd2
-- title:
--   Dubner's search: the multiples of $6$ up to $2\cdot10^{10}$ that are not sums of two middle numbers
-- statement:
--   **Dubner's search results.** Let $N$ be a multiple of $6$ with $6<N\le 2\cdot10^{10}$. Then $N$ is **not** a sum $N=m_1+m_2$ of two middle numbers $m_1,m_2>4$ exactly when
--
--   $$N\in\{96, 402, 516, 786, 906, 1116, 1146, 1266, 1356, 3246, 4206\}.$$
--
--   This is the computational evidence behind Conjectures 3a and 4a: the largest exception is $4206$.
-- source:
--   H. Dubner, Twin Prime Conjectures, J. Recreational Math. 30(3) (1999-2000); scan https://oeis.org/A007534/a007534.pdf, p. 2, Section 3 (Search Results)

import Mathlib
import Definitions.Def_Dubner_TwinPrimes

namespace Dubner
theorem search_results :
    ∀ N : ℕ, 6 ∣ N → 6 < N → N ≤ 20000000000 →
      ((¬ ∃ m₁ m₂ : ℕ, 4 < m₁ ∧ 4 < m₂ ∧ IsMiddleNumber m₁ ∧ IsMiddleNumber m₂ ∧ N = m₁ + m₂) ↔
        N ∈ ({96, 402, 516, 786, 906, 1116, 1146, 1266, 1356, 3246, 4206} : Finset ℕ)) := by
  sorry
end Dubner
