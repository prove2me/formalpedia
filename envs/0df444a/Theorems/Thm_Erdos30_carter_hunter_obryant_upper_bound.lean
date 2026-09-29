-- Prove2me | Theorems.Thm_Erdos30_carter_hunter_obryant_upper_bound
-- name    : Erdos30.carter_hunter_obryant_upper_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T17:57:35.638398+00:00
-- url     : https://prove2.me/theorems/8b1818fa-f15d-4139-9943-710622512c2b
-- title:
--   Carter–Hunter–O'Bryant: $h(N)\le\sqrt N+0.98183N^{1/4}+O(1)$
-- statement:
--   There is an absolute constant $C$ such that for every $N$,
--
--   $$h(N)\ \le\ \sqrt N+0.98183\,N^{1/4}+C.$$
--
--   This is the current record upper bound. Equivalently, a Sidon set with $k$ elements has diameter at least $k^2-bk^{3/2}-O(k)$ with $b\le1.96365$. The proof uses substantial computer assistance.
-- source:
--   D. Carter, Z. Hunter, K. O'Bryant, On the diameter of finite Sidon sets, arXiv:2310.20032 (2023), https://arxiv.org/abs/2310.20032 (abstract: "a Sidon set with diameter n has at most n^{1/2}+0.98183 n^{1/4}+O(1) elements"); cited at Erdős Problem #30, https://www.erdosproblems.com/30 as [CHO25], "the current record"

import Mathlib
import Definitions.Def_Erdos30Basic

namespace Erdos30

theorem carter_hunter_obryant_upper_bound :
    ∃ C : ℝ, ∀ N : ℕ, (h N : ℝ) ≤ Real.sqrt N + 0.98183 * (N : ℝ) ^ ((1 : ℝ) / 4) + C := by
  sorry

end Erdos30
