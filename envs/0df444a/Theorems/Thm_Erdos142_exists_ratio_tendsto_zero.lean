-- Prove2me | Theorems.Thm_Erdos142_exists_ratio_tendsto_zero
-- name    : Erdos142.exists_ratio_tendsto_zero
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:41:44.366411+00:00
-- url     : https://prove2.me/theorems/8d766ab3-6df2-4fc1-9a4c-90d8f20c46b4
-- title:
--   Erdős's separation question: $r_k(n)/r_{k+1}(n) \to 0$ for some $k \ge 3$
-- statement:
--   There exists $k \ge 3$ such that
--
--   $$\frac{r_k(n)}{r_{k+1}(n)} \;\longrightarrow\; 0 \qquad (n \to \infty).$$
--
--   In words: for at least one progression length $k \ge 3$, allowing progressions of length $k+1$ rather than $k$ lets a progression-free set be larger by an unbounded factor. Erdős observed in [Er80, p.92] that this is not known for any single $k \ge 3$ (here `[Er80]` is the erdosproblems.com bibliography key for Erdős's 1980 paper, not a reference to Erdős Problem #80) — the ratio is bounded below by a positive constant times $1$ only by the trivial monotonicity $r_k \le r_{k+1}$, and no separation at all has been established.
--
--   The question is a weakening of the main problem that isolates one specific consequence any asymptotic formula would have. If the formulas for $r_k$ and $r_{k+1}$ were known, comparing them would settle the ratio immediately; the fact that no separation is known for any $k$ measures precisely how little is understood about the dependence of $r_k$ on $k$. It is included in the mission as the smallest concrete open target attached to the problem.
--
--   **Formalization Note.** The existential quantifier over $k$ renders Erdős's phrase "for any $k \ge 3$" in the context "we do not even know whether ... for any $k \ge 3$", i.e. it suffices to exhibit one such $k$. Real division is Lean's, so the quotient is $0$ wherever $r_{k+1}(n) = 0$; this affects only $n = 0$ and is invisible to the `atTop` filter.
-- source:
--   Erdős Problem #142, https://www.erdosproblems.com/142 (cited there as [Er80, p.92], [Er81, p.4], [Er97c], [Va99, 1.27]); specifically the remark 'In [Er80] he remarks that we do not even know whether $r_k(n)/r_{k+1}(n)\to 0$ for any $k\geq 3$' (Erdos [Er80], p.92; [Er80] is the erdosproblems.com bibliography key for Erdos's 1980 paper, NOT Erdos Problem #80).

import Mathlib
import Definitions.Def_Erdos142Basic

namespace Erdos142

theorem exists_ratio_tendsto_zero :
    ∃ k : ℕ, 3 ≤ k ∧
      Filter.Tendsto (fun n : ℕ => (r k n : ℝ) / (r (k + 1) n : ℝ))
        Filter.atTop (nhds 0) := by sorry

end Erdos142
