-- Prove2me | Theorems.Thm_DynSetCover_lemma_6_3
-- name    : DynSetCover.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:47:06.299331+00:00
-- url     : https://prove2.me/theorems/32193662-fa05-4723-9d9b-b7f22ed6191a
-- title:
--   Lemma 6.3 — every selected operation lowers $\Phi$ and every $\Phi_i$, $i\le p$, by its work charge
-- statement:
--   Throughout, the states and update boundaries are those of admissible runs of the faster algorithm of §5 with capacity $N\ge2$ on valid update sequences keeping $|A_t|\le N$, with $L=\lceil\log_2(2N)\rceil$ and $\eta=1/L$.
--
--   Let $o$ be a selected internal operation in a state $s$, let $p$ be its priority evaluated in $s$, and let $s'$ be the result of executing it. Then
--   $$\Phi(s')\le\Phi(s)-w(o),\qquad \Phi_i(s')\le\Phi_i(s)-w(o)\ \text{ for every integer } i\le p,$$
--   where the work charge $w(o)$ is $1$ for an opening, commit or deletion and $\eta$ for a decrement continuation, starting increment or increment continuation.
--
--   Together with Lemma 6.2 this shows that the budget of $2048$ points removes the excess created by one update.
--
--   Differences from the source:
--   - generalization: a fixed family $\mathcal F$ of subsets of $U$ whose union is $U$ → an indexed family $(S_s)_{s<m}$ of subsets of $U$ with union $U$, in which two indices may carry the same subset; reason: the paper's family is an injectively indexed one; no step of the argument uses that the sets are distinct
--   - generalization: the run of the §5 algorithm with FIFO tie-breaking inside each priority and category, continuations moving the head element of a list, and one fixed cheapest set $S_e$ per element → every admissible run: any operation that is applicable and maximal in (priority, category order), any element of the list, and any choice of cheapest sets; reason: no proof in §§5–6 uses the FIFO or head-element rules or the particular cheapest set; the paper's run is one admissible run
--   - encoding: the lists $U_Q$, $R_Q$, $P_Q$ → finite sets of elements; reason: list order serves only the tie-breaking and head-element choices that the admissible runs leave free; membership is unchanged
--   - generalization: a selected internal operation (one that is executed) → every selected operation, including one whose work charge exceeds the remaining budget (its effect is still defined); reason: the proof uses only that the operation is maximal in (priority, category) in a state of the run, not that it fits the budget
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), Lemma 6.3, p.49 (PDF 51)

import Mathlib
import Definitions.Def_DynSetCover_Potential

namespace DynSetCover

/-- **Lemma 6.3 (Progress during internal operations)** (Paul, Solomon, STOC 2027 submission,
sha256 a671756b…, p.49 (PDF 51)). Let `p` be the priority of a selected internal operation,
evaluated before execution. The operation decreases `Φ`, and every `Φ_i` with `i ≤ p`, by at
least its work charge. The charge is `1` for an opening, commit, or deletion, and `η` for a
decrement continuation, starting increment, or increment continuation.

**Formalization Note.** "Selected" is `Selected` in a state of an admissible run; the claim is
about the state `exec s o` produced by executing it. The work charges are `charge`. -/
theorem lemma_6_3 (inst : Instance) (N : ℕ) (hN : 2 ≤ N) (ce : Fin inst.u → Fin inst.m)
    (hce : inst.IsCheapest ce) (s : State inst) (b : ℝ) (hs : IsState inst N ce s b)
    (o : Op inst) (ho : Selected inst N s o) :
    Phi inst N (exec inst s o) ≤ Phi inst N s - charge inst N o ∧
    ∀ i : ℤ, i ≤ prio inst s o →
      PhiTail inst N (exec inst s o) i ≤ PhiTail inst N s i - charge inst N o := by sorry

end DynSetCover
