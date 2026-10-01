-- Prove2me | Theorems.Thm_Erdos142_exists_ratio_isLittleO
-- name    : Erdos142.exists_ratio_isLittleO
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-30T21:41:12.293362+00:00
-- url     : https://prove2.me/theorems/234788a2-fdd1-46c2-8b08-9a9aa4a45b81
-- title:
--   Erdős separation in little-o form
-- statement:
--   There exists a natural number k ≥ 3 such that the extremal progression-free counting function r_k is little-o of r_{k+1} along the natural numbers:
--
--   $$\exists k\ge 3,\quad (n\mapsto r_k(n))=o(n\mapsto r_{k+1}(n)).$$
--
--   This is the quantitative separation core of Erdős's question. It isolates the combinatorial assertion from the later analytic conversion of little-o notation into the limit of the quotient r_k(n)/r_{k+1}(n).
-- source:
--   Erdős Problem #142, https://www.erdosproblems.com/142, [Er80, p.92]: the remark that it is unknown whether r_k(n)/r_{k+1}(n) tends to 0 for any k ≥ 3.

import Mathlib
import Definitions.Def_Erdos142Basic

namespace Erdos142

theorem exists_ratio_isLittleO :
    ∃ k : ℕ, 3 ≤ k ∧
      (fun n : ℕ => (r k n : ℝ)) =o[Filter.atTop]
        (fun n : ℕ => (r (k + 1) n : ℝ)) := by sorry

end Erdos142
