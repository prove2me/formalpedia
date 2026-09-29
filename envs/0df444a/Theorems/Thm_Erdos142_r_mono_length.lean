-- Prove2me | Theorems.Thm_Erdos142_r_mono_length
-- name    : Erdos142.r_mono_length
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:37:04.092465+00:00
-- url     : https://prove2.me/theorems/e1d1a938-80dd-486a-80a0-1e6b26570c22
-- title:
--   $r_k(N)$ is non-decreasing in the progression length $k$
-- statement:
--   If $2 \le k \le l$ then for every $N$,
--
--   $$r_k(N) \;\le\; r_l(N).$$
--
--   The reason is that a set avoiding progressions of length $k$ automatically avoids the longer ones: any non-trivial $l$-term progression contains a non-trivial $k$-term progression with the same first term and common difference, so every $k$-AP-free set is $l$-AP-free, and the family over which the maximum defining $r_k(N)$ is taken is contained in the family defining $r_l(N)$.
--
--   This monotonicity is the elementary reason why lower bounds propagate upward in $k$ — Behrend's bound for $k = 3$ is inherited by every $k \ge 3$ — and why upper bounds propagate downward. It is used throughout the subject without comment, and having it available in the mission's notation avoids re-deriving it inside longer arguments.
--
--   **Formalization Note.** The hypothesis $2 \le k$ is required and is not cosmetic. Under the source convention, progressions of length $0$ and $1$ are trivial, so every set is free of them and $r_0(N) = r_1(N) = N$, whereas $r_2(N) = 1$ for $N \ge 1$. Monotonicity therefore fails across the boundary $k = 1 \to k = 2$ and holds only from $k \ge 2$ onward.
-- source:
--   Erdős Problem #142, https://www.erdosproblems.com/142 (cited there as [Er80, p.92], [Er81, p.4], [Er97c], [Va99, 1.27]); standard elementary property of the function $r_k$.

import Mathlib
import Definitions.Def_Erdos142Basic

namespace Erdos142

theorem r_mono_length (k l N : ℕ) (hk : 2 ≤ k) (h : k ≤ l) : r k N ≤ r l N := by sorry

end Erdos142
