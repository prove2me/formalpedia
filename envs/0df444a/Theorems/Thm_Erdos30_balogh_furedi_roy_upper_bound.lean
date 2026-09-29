-- Prove2me | Theorems.Thm_Erdos30_balogh_furedi_roy_upper_bound
-- name    : Erdos30.balogh_furedi_roy_upper_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T17:51:50.710764+00:00
-- url     : https://prove2.me/theorems/93eaf6a3-c186-4678-aeed-619240feba25
-- title:
--   Balogh–Füredi–Roy: $h(N)\le\sqrt N+0.998N^{1/4}$ for large $N$
-- statement:
--   There is $N_0$ such that for all $N\ge N_0$,
--
--   $$h(N)\ \le\ \sqrt N+0.998\,N^{1/4}.$$
--
--   This was the first improvement of the constant $1$ in the Erdős–Turán–Lindström bound, by combining two elementary counting arguments.
-- source:
--   J. Balogh, Z. Füredi, S. Roy, An upper bound on the size of Sidon sets, Amer. Math. Monthly 130 (2023), arXiv:2103.15850, https://arxiv.org/abs/2103.15850 (main theorem, abstract: "the maximum size of a Sidon set of {1,2,…,n} is at most √n + 0.998 n^{1/4} for sufficiently large n"); cited at Erdős Problem #30, https://www.erdosproblems.com/30 as [BFR21]

import Mathlib
import Definitions.Def_Erdos30Basic

namespace Erdos30

theorem balogh_furedi_roy_upper_bound :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (h N : ℝ) ≤ Real.sqrt N + 0.998 * (N : ℝ) ^ ((1 : ℝ) / 4) := by
  sorry

end Erdos30
