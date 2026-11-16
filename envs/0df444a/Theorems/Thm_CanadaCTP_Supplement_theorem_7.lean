-- Prove2me | Theorems.Thm_CanadaCTP_Supplement_theorem_7
-- name    : CanadaCTP.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:40:17.123026+00:00
-- url     : https://prove2.me/theorems/e6d7a594-0335-415a-bd18-a168a24f190d
-- title:
--   Theorem 7 — no policy entering each path at most $k$ times is an $O(1)$-approximation
-- statement:
--   Consider disjoint-path graphs. For every $k\in\mathbb N$, there is no algorithm that enters each path at most $k$ times and that is an $O(1)$-approximation.
--
--   Precisely: for every $k\in\mathbb N$ ($k=0$ included) and every constant $C$ there is a CTP instance on a disjoint-path graph such that every feasible policy that enters each path at most $k$ times has
--   $$\mathbb E[\pi]>C\cdot\mathbb E[\mathrm{Opt}].$$
--
--   So a constant-factor approximation must be able to return to a path an unbounded number of times, as ParallelTraveller does with its doubling budgets.
--
--   **Formalization Note** Policies are the published randomized stateful policies; an entry is a move from $s$ onto the first edge of a path, counted along every positive-probability trajectory.
--
--   Differences from the source:
--   - encoding: no algorithm entering each path at most k times is an O(1)-approximation → ∀ C, ∃ instance I, ∀ feasible π entering each path at most k times, C·E[Opt] < E[π]; reason: an algorithm maps instances to feasible policies; by choice the negation of ∃C ∀I E[Alg(I)] ≤ C·E[Opt] is equivalent to this form
--   - reading: k ∈ ℕ → every k : ℕ, including k = 0; reason: the paper uses both ℕ₀ (p.20) and ℕ_{>0} (p.22), so ℕ is ambiguous; the Lean covers both readings (at k = 0 no feasible policy exists, since reaching t needs an entry)
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Theorem 7, p.30 (Appendix A, proof pp.30–31)

import Mathlib
import Definitions.Def_CanadaCTP_Supplement_Entries

namespace CanadaCTP.Supplement

open CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33),
Theorem 7, p.30 (Appendix A, proof pp.30–31): "Consider disjoint-paths graphs. For every k ∈ N,
there is no algorithm that enters each path at most k times and that is an O(1)-approximation."

For every `k : ℕ` (`k = 0` included: no feasible policy makes zero entries) and every
constant `C` there is a CTP instance on a disjoint-path graph on which
every feasible policy (randomized, stateful) that enters each path at most `k` times has expected
cost strictly larger than `C · E[Opt]`.

**Formalization Note.** An algorithm is an `O(1)`-approximation if there is a constant `C` with
`E[Alg] ≤ C·E[Opt]` on every instance; the statement is the negation for every map from instances
to feasible entry-bounded policies (equivalent by choice). Entries are counted along every
positive-probability trajectory (`EntryBounded`). -/
theorem theorem_7 :
    ∀ k : ℕ, ∀ C : ℝ, ∃ I : Inst, I.IsCTP ∧
      ∀ (Mem : Type) (π : Policy I Mem), Feasible I π → EntryBounded I π k →
        ENNReal.ofReal C * optCost I < expCost I π := by sorry

end CanadaCTP.Supplement
