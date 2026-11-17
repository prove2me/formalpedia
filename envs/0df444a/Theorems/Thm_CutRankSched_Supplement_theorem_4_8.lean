-- Prove2me | Theorems.Thm_CutRankSched_Supplement_theorem_4_8
-- name    : CutRankSched.Supplement.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:52:20.732739+00:00
-- url     : https://prove2.me/theorems/4f0c3498-daf3-4e5a-a2a4-cd829d87dd37
-- title:
--   Theorem 4.8 — exactness within the fixed-gadget compilation class
-- statement:
--   Consider a valid instance and the class of compilations that retain each extracted rotation exactly once, change the trace solely by adjacent commuting swaps, assign each event its prescribed exposure gadget, and group the events into consecutive rounds of pairwise vertex-disjoint exposures. Within this class the minimum number of non-Clifford rounds exists and equals the optimum of Problem 3.2:
--   $$
--   \min\{\,k : \text{some compilation in the class has } k \text{ rounds}\,\} \;=\; \min\{\,L : \exists\,\lambda:[n]\to[L] \text{ satisfying (2)}\,\}.
--   $$
--   Both sides are $0$ when $n=0$.
--
--   Problem 3.2 is therefore not a relaxation: inside this conservative compilation class its optimum is the true minimum round count.
--
--   Differences from the source:
--   - reading: compilations that retain each extracted rotation exactly once, change their trace solely by adjacent commuting swaps, assign each event its prescribed exposure gadget, and group events into rounds of pairwise disjoint exposures → FixedGadgetCompilation: a list of rounds whose concatenation is reachable from the trace order by adjacent swaps of events with A_ab = 0, with vertex-disjoint exposures inside each round; reason: the class is defined by these combinatorial conditions, as the proof uses it; reachability from the trace order makes each rotation appear exactly once
--   - encoding: the minimum number of non-Clifford rounds equals the optimum of 3.2 → IsLeast {k | some compilation has k rounds} (sInf {L | Feasible I L}); reason: the optimum min max_i λ_i (0 when n = 0) is the least L with a feasible λ : Fin n → Fin L; IsLeast also asserts the minimum is attained
--   - encoding: events 1..n and layers [L] = {1..L} → Fin n and Fin L (0-based); reason: index shift; same instances and assignments
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 4.8, p.7

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Instance_Valid
import Definitions.Def_CutRankSched_Feasible
import Definitions.Def_CutRankSched_Supplement_FixedGadgetCompilation

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- **Theorem 4.8 (Exactness within the fixed-gadget compilation class)** (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 4.8,
p.7). Consider only compilations that retain each extracted rotation exactly once, change their
trace solely by adjacent commuting swaps, assign each event its prescribed exposure gadget, and
group events into rounds of pairwise disjoint exposures. Within this class, the minimum number of
non-Clifford rounds equals the optimum of Problem 3.2.

Stated as: for a valid instance, the least number of rounds of a fixed-gadget compilation exists
and is the least `L` such that the instance is feasible in `L` rounds.

**Formalization Note** The optimum of Problem 3.2, `min max_i λ_i` (zero when `n = 0`), is the least
`L` with `Feasible I L` (0-based layers `Fin L`). The class is combinatorial
(`FixedGadgetCompilation`). -/
theorem theorem_4_8 (I : Instance) (hI : I.Valid) :
    IsLeast {k : ℕ | ∃ R : List (List (Fin I.n)), FixedGadgetCompilation I R ∧ R.length = k}
      (sInf {L : ℕ | Feasible I L}) := by sorry

end Supplement

end CutRankSched
