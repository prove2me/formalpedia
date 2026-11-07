-- Prove2me | Theorems.Thm_DynConnWC_theorem_23
-- name    : DynConnWC.theorem_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:39:26.87618+00:00
-- url     : https://prove2.me/theorems/2fd9a279-5212-4293-8ac0-a4d2aa8f8d5f
-- title:
--   Theorem 23 — all answers correct w.p. $\ge1-n^{-\beta}$, with the parameters of §4.6
-- statement:
--   Fix $d,\beta>0$ and $n\ge2$, with $T_0=\lceil n^d\rceil$ and $\delta=n^{-\beta}$.
--
--   1. §4.6's $k$ is even and at least $2$, and its $w$ is at least $J$.
--   2. §4.6's choices of $k,r,w$ satisfy the budget (2)–(5).
--   3. For every setup meeting the standing assumptions and the budget, and every valid operation sequence with at most $T_0$ updates, fixed in advance and interleaved with any number of queries, all query answers of the algorithm are correct with probability at least $1-n^{-\beta}$.
--
--   Together these give the theorem on the page for exactly the parameters of §4.6.
--
--   Differences from the source:
--   - generalization: the parameters chosen in §4.6 → any parameters with $k$ even, $k\ge2$, $w\ge J$ satisfying (2)–(5), and any selector and search mode meeting the specification; reason: the source's proof uses only (2)–(5); clauses 1 and 2 give the source's parameters as an instance
--   - encoding: $\log_2$, $\ln$, ceilings → `Real.logb 2`, `Real.log`, `Nat.ceil`; reason: these are the same real numbers
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Theorem 23 and (2)–(5), p.23 (PDF 24)

import Mathlib
import Definitions.Def_DynConnWC_Events

set_option autoImplicit false

namespace DynConnWC

/-- **Theorem 23 (Correctness).** King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027 submission, sha256 9d16c13e…), p.23 (PDF 24), with the parameters of §4.6.
"For every update sequence of at most T0 updates, fixed in advance and interleaved with any number of
queries, all query answers are correct with probability at least 1 − n^{−β}."

**Formalization Note.** Three clauses. First, §4.6's `k` is even and at least `2` and its `w` is at
least `J`. Second, §4.6's choices of `k, r, w` satisfy the budget (2)–(5). Third, every setup meeting the
standing assumptions and the budget answers all queries of a fixed valid sequence with at most
`T0 = ⌈n^d⌉` updates correctly with probability at least `1 − n^{−β}`. Together they give the page's
statement for exactly §4.6's parameters. The third clause also covers other parameters meeting (2)–(5),
which is what the program of Lemma 24 uses (for real `d, β` the exact ceilings need not be computable). -/
theorem theorem_23 (d β : ℝ) (hd : 0 < d) (hβ : 0 < β) {n : ℕ} (hn : 2 ≤ n) :
    (Even (k46 n d β) ∧ 2 ≤ k46 n d β ∧ Jbits n ≤ w46 n d β) ∧
    (∀ S : AlgSetup n, Params46 S d β → Budget S (T0par n d) (deltaPar n β)) ∧
    (∀ S : AlgSetup n, S.Wf → Budget S (T0par n d) (deltaPar n β) →
      ∀ ops : List (Op n), Valid ops → numUpdates ops ≤ T0par n d →
        1 - deltaPar n β ≤ probR S {R | AlgAllCorrect S R ops}) := by sorry

end DynConnWC
