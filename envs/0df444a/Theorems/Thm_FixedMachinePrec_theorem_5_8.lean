-- Prove2me | Theorems.Thm_FixedMachinePrec_theorem_5_8
-- name    : FixedMachinePrec.theorem_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:07:31.802861+00:00
-- url     : https://prove2.me/theorems/1690c8a5-ae80-4af6-b098-5c6c982c6c27
-- title:
--   Theorem 5.8 — a hierarchy described by $(\mathcal F_{4m+5},\mathcal F_{m+3})$
-- statement:
--   Let $m\ge3$, let $\prec$ be a strict partial order on $J=\{1,\dots,N\}$, let $\mathrm{rank}$ be a bijective topological rank, and suppose $J$ has a feasible full schedule. Then $J$ has a hierarchy in the sense of Definition 5.7 such that
--
--   1. every node set is represented exactly, on all of $J$, by a Boolean formula with at most $4m+5$ atomic occurrences;
--   2. for each marked slot, its prefix in its node $W$ is $W\cap C$ for a set $C$ with a global Boolean description with at most $m+3$ atomic occurrences;
--   3. every nonempty node has at least one marked full slot, and every child has at most $|W|-m$ jobs.
--
--   That is, $J$ is the root of a hierarchy described by $(\mathcal F_{4m+5},\mathcal F_{m+3})$. This is the structural heart of the correctness proof (all of Section 7).
--
--   **Formalization Note** Clause 3 is built into the definition of a described hierarchy.
--
--   Differences from the source:
--   - generalization: the rank of the smallest-identifier topological order → every bijective topological rank; reason: every topological rank is the smallest-identifier rank after relabelling jobs by their ranks, so each case is an instance of the source's statement
--   - encoding: jobs 1, …, n and padded jobs 1, …, N → Fin n and Fin N (0-based labels); reason: Lean convention; the shift changes no instance
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Theorem 5.8, p.17

import Mathlib
import Definitions.Def_FixedMachinePrec_Formula
import Definitions.Def_FixedMachinePrec_Hierarchy

namespace FixedMachinePrec

/-- **Theorem 5.8 (A hierarchy with bounded global descriptions).** Jansen, *Precedence Constraint
Scheduling on a Fixed Number of Machines* (manuscript, sha256 08cdf3e1…), Theorem 5.8, p.17: "Let
m ≥ 3. Every feasible full instance has a hierarchy in the sense of Definition 5.7 such that every
node set is represented exactly, on the entire ground set J, by a Boolean formula with at most
4m + 5 atomic occurrences. For each marked slot, its prefix in its node W is W ∩ C, where C has a
global Boolean description with at most m + 3 atomic occurrences. The atoms are the boundary sets,
global predecessor and successor cones, weak cones, rank suffixes, and constants already used by
GenerateFamily. Every nonempty node has at least one marked full slot, and every child has at most
|W| − m jobs."

Let `m ≥ 3`, let `≺` be a strict partial order on `J = Fin N` with a bijective topological rank,
and suppose `J` has a feasible full schedule. Then `J` is the root of a hierarchy described by
`(F_{4m+5}, F_{m+3})`.

**Formalization Note** The theorem is stated for every bijective topological rank; the algorithm's
smallest-identifier rank is one of them, and every topological rank is the smallest-identifier rank
after relabelling the jobs by their ranks, so this is the paper's statement. The last sentence is
built into `Described` (a nonempty node has a nonempty list of marks, and every gap misses the `m`
jobs of a marked slot). -/
theorem theorem_5_8 {N : ℕ} (m : ℕ) (hm : 3 ≤ m) (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (hprec : IsStrictOrder' prec) (rank : Fin N → ℕ) (hrank : IsTopoRank prec rank)
    (hfeas : ∃ S : List (Finset (Fin N)), IsFullSchedule prec m Finset.univ S) :
    Described prec m (family prec rank m (4 * m + 5)) (family prec rank m (m + 3)) Finset.univ := by sorry

end FixedMachinePrec
