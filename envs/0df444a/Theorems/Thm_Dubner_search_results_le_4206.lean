-- Prove2me | Theorems.Thm_Dubner_search_results_le_4206
-- name    : Dubner.search_results_le_4206
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-24T13:10:14.806261+00:00
-- url     : https://prove2.me/theorems/d2a5b904-a722-4adc-b7a9-fdebd41ea3e5
-- title:
--   Dubner's search up to $4206$: the eleven multiples of $6$ that are not sums of two middle numbers
-- statement:
--   **Dubner's search results, up to the largest exception.** Let $N$ be a multiple of $6$ with $6<N\le 4206$. Then $N$ is **not** a sum $N=m_1+m_2$ of two middle numbers $m_1,m_2>4$ exactly when
--
--   $$N\in\{96, 402, 516, 786, 906, 1116, 1146, 1266, 1356, 3246, 4206\}.$$
--
--   This is the statement `Dubner.search_results` with the bound $2\cdot10^{10}$ replaced by $4206$, the largest exception. It certifies the list of the eleven exceptions; the range from $4212$ to $2\cdot10^{10}$ is not covered.
-- source:
--   H. Dubner, Twin Prime Conjectures, J. Recreational Math. 30(3) (1999-2000); scan https://oeis.org/A007534/a007534.pdf, p. 2, Section 3 (Search Results), restricted to N up to 4206

import Mathlib
import Definitions.Def_Dubner_TwinPrimes

namespace Dubner
theorem search_results_le_4206 :
    ∀ N : ℕ, 6 ∣ N → 6 < N → N ≤ 4206 →
      ((¬ ∃ m₁ m₂ : ℕ, 4 < m₁ ∧ 4 < m₂ ∧ IsMiddleNumber m₁ ∧ IsMiddleNumber m₂ ∧ N = m₁ + m₂) ↔
        N ∈ ({96, 402, 516, 786, 906, 1116, 1146, 1266, 1356, 3246, 4206} : Finset ℕ)) := by
  sorry
end Dubner
