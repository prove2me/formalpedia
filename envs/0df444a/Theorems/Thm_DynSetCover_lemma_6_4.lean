-- Prove2me | Theorems.Thm_DynSetCover_lemma_6_4
-- name    : DynSetCover.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:47:40.734197+00:00
-- url     : https://prove2.me/theorems/f2a79d72-f29f-46e2-bae7-f8f47f3d7ba5
-- title:
--   Lemma 6.4 — cutoff certificate $\Phi_i\le 500\,g_i(A)$
-- statement:
--   Throughout, the states and update boundaries are those of admissible runs of the faster algorithm of §5 with capacity $N\ge2$ on valid update sequences keeping $|A_t|\le N$, with $L=\lceil\log_2(2N)\rceil$ and $\eta=1/L$.
--
--   Let $i$ be an integer cutoff and $A$ the active set of a state $s$. Then
--   1. if $s$ is clean at $i$, then $\Phi_i(s)\le 500\,g_i(A)$;
--   2. if $o$ is a selected internal operation in $s$ of priority below $i$ and $s'$ is the result of executing it, then $\Phi_i(s')\le 500\,g_i(A)$, whether or not $s'$ is clean at $i$.
--
--   The certificate links the scheduler to the potential: whenever $\Phi_i$ exceeds $1024\,g_i$, some operation of priority at least $i$ must be applicable.
--
--   Differences from the source:
--   - generalization: a fixed family $\mathcal F$ of subsets of $U$ whose union is $U$ → an indexed family $(S_s)_{s<m}$ of subsets of $U$ with union $U$, in which two indices may carry the same subset; reason: the paper's family is an injectively indexed one; no step of the argument uses that the sets are distinct
--   - generalization: the run of the §5 algorithm with FIFO tie-breaking inside each priority and category, continuations moving the head element of a list, and one fixed cheapest set $S_e$ per element → every admissible run: any operation that is applicable and maximal in (priority, category order), any element of the list, and any choice of cheapest sets; reason: no proof in §§5–6 uses the FIFO or head-element rules or the particular cheapest set; the paper's run is one admissible run
--   - encoding: the lists $U_Q$, $R_Q$, $P_Q$ → finite sets of elements; reason: list order serves only the tie-breaking and head-element choices that the admissible runs leave free; membership is unchanged
--   - generalization: a selected internal operation (one that is executed) → every selected operation, including one whose work charge exceeds the remaining budget (its effect is still defined); reason: the proof uses only that the operation is maximal in (priority, category) in a state of the run, not that it fits the budget
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), Lemma 6.4, p.52 (PDF 54)

import Mathlib
import Definitions.Def_DynSetCover_Potential

namespace DynSetCover

/-- **Lemma 6.4 (Cutoff certificate)** (Paul, Solomon, STOC 2027 submission, sha256 a671756b…,
p.52 (PDF 54)). For every integer cutoff `i`, `Φ_i ≤ 500 g_i(A)` holds whenever the state is
clean at `i`, and immediately after any selected internal operation of priority below `i`. In
the latter case, the resulting state need not be clean at `i`.

**Formalization Note.** The second clause concerns the state `exec s o` produced by a selected
operation `o` of priority `< i` in a state `s` of an admissible run; no cleanliness of
`exec s o` is assumed. `A` is the active set, which internal operations do not change. -/
theorem lemma_6_4 (inst : Instance) (N : ℕ) (hN : 2 ≤ N) (ce : Fin inst.u → Fin inst.m)
    (hce : inst.IsCheapest ce) (s : State inst) (b : ℝ) (hs : IsState inst N ce s b) (i : ℤ) :
    (CleanAt inst N s i → PhiTail inst N s i ≤ 500 * inst.g i s.active) ∧
    (∀ o, Selected inst N s o → prio inst s o < i →
      PhiTail inst N (exec inst s o) i ≤ 500 * inst.g i (exec inst s o).active) := by sorry

end DynSetCover
