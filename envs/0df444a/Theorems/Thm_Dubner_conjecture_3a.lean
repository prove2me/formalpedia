-- Prove2me | Theorems.Thm_Dubner_conjecture_3a
-- name    : Dubner.conjecture_3a
-- status  : Open
-- author  : @Idealson
-- created : 2026-11-24T11:08:36.837946+00:00
-- url     : https://prove2.me/theorems/9a817662-9347-4104-8048-85e5157d5e97
-- title:
--   Dubner's Conjecture 3a: multiples of $6$ above $4206$ are sums of two middle numbers
-- statement:
--   **Dubner's Conjecture 3a.** Every multiple of $6$ greater than $4206$ is the sum of two middle numbers, where a middle number is an integer $m$ with $m-1$ and $m+1$ both prime:
--
--   $$\forall N>4206,\ 6\mid N \implies \exists\, m_1,m_2 \text{ middle numbers with } N=m_1+m_2.$$
--
--   Dubner writes that Conjecture 3a, with a little extra data, implies all his other conjectures. The implication to Conjecture 4a needs no extra data.
-- source:
--   H. Dubner, Twin Prime Conjectures, J. Recreational Math. 30(3) (1999-2000); scan https://oeis.org/A007534/a007534.pdf, p. 2, Section 2, Conjecture 3a

import Mathlib
import Definitions.Def_Dubner_TwinPrimes

namespace Dubner
theorem conjecture_3a :
    ∀ N : ℕ, 6 ∣ N → 4206 < N →
      ∃ m₁ m₂ : ℕ, IsMiddleNumber m₁ ∧ IsMiddleNumber m₂ ∧ N = m₁ + m₂ := by
  sorry
end Dubner
