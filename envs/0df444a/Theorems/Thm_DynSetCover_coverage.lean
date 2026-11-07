-- Prove2me | Theorems.Thm_DynSetCover_coverage
-- name    : DynSetCover.coverage
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:46:16.302647+00:00
-- url     : https://prove2.me/theorems/40aaabd7-792d-4023-b9e4-d55f86bd7c66
-- title:
--   §5 — the maintained cover is feasible at every state
-- statement:
--   Throughout, the states and update boundaries are those of admissible runs of the faster algorithm of §5 with capacity $N\ge2$ on valid update sequences keeping $|A_t|\le N$, with $L=\lceil\log_2(2N)\rceil$ and $\eta=1/L$.
--
--   At every state (in particular at every update boundary), every active element $e$ is assigned to a retained copy $Q$, that is $e\in U_Q\cup R_Q$, whose underlying set contains $e$. Consequently the physical cover covers the active set $A_t$.
--
--   This is the feasibility half of the algorithm's guarantee: the algorithm always returns a cover.
--
--   Differences from the source:
--   - generalization: a fixed family $\mathcal F$ of subsets of $U$ whose union is $U$ → an indexed family $(S_s)_{s<m}$ of subsets of $U$ with union $U$, in which two indices may carry the same subset; reason: the paper's family is an injectively indexed one; no step of the argument uses that the sets are distinct
--   - generalization: the run of the §5 algorithm with FIFO tie-breaking inside each priority and category, continuations moving the head element of a list, and one fixed cheapest set $S_e$ per element → every admissible run: any operation that is applicable and maximal in (priority, category order), any element of the list, and any choice of cheapest sets; reason: no proof in §§5–6 uses the FIFO or head-element rules or the particular cheapest set; the paper's run is one admissible run
--   - encoding: the lists $U_Q$, $R_Q$, $P_Q$ → finite sets of elements; reason: list order serves only the tie-breaking and head-element choices that the admissible runs leave free; membership is unchanged
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), §5, What is the motivation for Modification 3?, p.42 (PDF 44)

import Mathlib
import Definitions.Def_DynSetCover_Algorithm

namespace DynSetCover

/-- **§5, coverage** (Paul, Solomon, STOC 2027 submission, sha256 a671756b…, p.42 (PDF 44)).
"Coverage is preserved throughout, since increments do not change assignments, and an element
pending reassignment remains assigned to its previous copy until its transfer executes.
Therefore the algorithm always returns a feasible cover at each update boundary."

At every state of an admissible run (in particular at every update boundary), every active
element is assigned (in `U_Q ∪ R_Q`) to a retained copy `Q` whose underlying set contains it;
hence the physical cover covers the active set. -/
theorem coverage (inst : Instance) (N : ℕ) (hN : 2 ≤ N) (ce : Fin inst.u → Fin inst.m)
    (hce : inst.IsCheapest ce) (s : State inst) (b : ℝ) (hs : IsState inst N ce s b) :
    (∀ e ∈ s.active, ∃ Q ∈ s.copies, e ∈ cov inst s Q ∧ e ∈ inst.S Q.2) ∧
    inst.Covers (physCover inst s) s.active := by sorry

end DynSetCover
