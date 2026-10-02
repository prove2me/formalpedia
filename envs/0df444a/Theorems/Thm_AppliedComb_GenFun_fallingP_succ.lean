-- Prove2me | Theorems.Thm_AppliedComb_GenFun_fallingP_succ
-- name    : AppliedComb.GenFun.fallingP_succ
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:11:43.124982+00:00
-- url     : https://prove2.me/theorems/62f4283e-0b6f-42b3-b3a2-55c91dc42c96
-- title:
--   Lemma 8.11 — P(p, k + 1) = P(p, k)(p − k)
-- statement:
--   Let $P(p, k)$ be the number of Definition 8.8, defined for real $p$ and nonnegative integers $k$ by $P(p, 0) = 1$ and $P(p, k) = p\,P(p-1, k-1)$ for $k > 0$. Then for every real number $p$ and every integer $k \ge 0$,
--
--   $$P(p, k + 1) = P(p, k)\,(p - k).$$
--
--   The definition peels off the *first* factor of $p(p-1)\cdots(p-k)$; this lemma peels off the *last* one. It is the recursion used to compute $C(-1/2, k)$ in Lemma 8.12.
--
--   **Formalization Note.** $P$ is `AppliedComb.GenFun.fallingP`; $k$ is a natural number and is cast to $\mathbb{R}$ in $p - k$.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 166, Lemma 8.11

import Mathlib
import Definitions.Def_AppliedComb_GenFun_binomReal

namespace AppliedComb.GenFun

/-- Keller–Trotter, Lemma 8.11 (p. 166): for each `k ≥ 0`, `P(p, k + 1) = P(p, k)(p - k)`,
for every real number `p`, where `P` is the recursion of Definition 8.8. -/
theorem fallingP_succ (p : ℝ) (k : ℕ) :
    fallingP p (k + 1) = fallingP p k * (p - k) := by sorry

end AppliedComb.GenFun
