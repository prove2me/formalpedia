-- Prove2me | Theorems.Thm_Erdos30_obryant_upper_bound
-- name    : Erdos30.obryant_upper_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T17:52:19.161664+00:00
-- url     : https://prove2.me/theorems/d8d36ff6-67a4-4b02-aa24-3a2cf3589d66
-- title:
--   O'Bryant: $h(N)\le\sqrt N+0.99703N^{1/4}$ for large $N$
-- statement:
--   There is $N_0$ such that for all $N\ge N_0$,
--
--   $$h(N)\ \le\ \sqrt N+0.99703\,N^{1/4}.$$
--
--   This is a slight numerical improvement on Balogh–Füredi–Roy obtained by a logically simpler method; equivalently, a Sidon set with $k$ elements has diameter at least $k^2-1.99405k^{3/2}$ for large $k$.
-- source:
--   K. O'Bryant, On the size of finite Sidon sets, arXiv:2207.07800 (2022), https://arxiv.org/abs/2207.07800 (abstract: "if n is sufficiently large, then the largest subset of {1,2,…,n} that is a Sidon set has cardinality at most n^{1/2}+0.99703 n^{1/4}"); cited at Erdős Problem #30, https://www.erdosproblems.com/30 as [OB22]

import Mathlib
import Definitions.Def_Erdos30Basic

namespace Erdos30

theorem obryant_upper_bound :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (h N : ℝ) ≤ Real.sqrt N + 0.99703 * (N : ℝ) ^ ((1 : ℝ) / 4) := by
  sorry

end Erdos30
