-- Prove2me | Theorems.Thm_DynSetCover_lemma_5_1
-- name    : DynSetCover.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:46:04.092253+00:00
-- url     : https://prove2.me/theorems/4d3c46f2-bd4e-4a81-bad3-0557ef07ab03
-- title:
--   Lemma 5.1 — level bounds and protection of pending elements
-- statement:
--   Throughout, the states and update boundaries are those of admissible runs of the faster algorithm of §5 with capacity $N\ge2$ on valid update sequences keeping $|A_t|\le N$, with $L=\lceil\log_2(2N)\rceil$ and $\eta=1/L$.
--
--   At every state:
--   1. **Level bounds.** Every retained copy $Q$ (including an empty one) satisfies $H(S_Q)-L\le q_Q\le h_Q\le H(S_Q)$; every element $e$ assigned to $Q$ satisfies $q_Q\le\ell(e)\le h_Q\le b(e)$; every active element satisfies $b(e)-L\le\ell(e)\le b(e)$; and $R_Q\neq\emptyset$ implies $q_Q<h_Q$.
--   2. **Pending-list structure.** At most one of $P_Q$, $R_Q$ is nonempty. If $P_Q\ne\emptyset$ then $q_Q=h_Q$ and $\ell(e)=h_Q+1\le b(e)$ for $e\in P_Q$. The sets $P_Q\cup U_Q$, over the copies with $P_Q\neq\emptyset$, are pairwise disjoint.
--   3. **Protection of pending elements.** An element of $P_Q$ stays in $P_Q$ (and $Q$ stays retained) with the same actual level under every executed operation other than the decrement continuation into $Q$ that transfers it, and under every input update other than its own departure. Immediately before any selected operation: (a) an opening selects a batch $S\cap A_t(r)$ disjoint from $P_Q\cup U_Q$ for every copy $Q$ with $P_Q\neq\emptyset$; (b) a copy selected for a starting increment, increment continuation, commit or deletion has no assigned element in any pending list.
--
--   These invariants underlie the potential analysis of §6 and the window of levels used by the implementation of §7.
--
--   **Formalization Note** "Assigned to $Q$" means membership in $U_Q\cup R_Q$. Input updates are applied at update boundaries.
--
--   Differences from the source:
--   - generalization: a fixed family $\mathcal F$ of subsets of $U$ whose union is $U$ → an indexed family $(S_s)_{s<m}$ of subsets of $U$ with union $U$, in which two indices may carry the same subset; reason: the paper's family is an injectively indexed one; no step of the argument uses that the sets are distinct
--   - generalization: the run of the §5 algorithm with FIFO tie-breaking inside each priority and category, continuations moving the head element of a list, and one fixed cheapest set $S_e$ per element → every admissible run: any operation that is applicable and maximal in (priority, category order), any element of the list, and any choice of cheapest sets; reason: no proof in §§5–6 uses the FIFO or head-element rules or the particular cheapest set; the paper's run is one admissible run
--   - encoding: the lists $U_Q$, $R_Q$, $P_Q$ → finite sets of elements; reason: list order serves only the tie-breaking and head-element choices that the admissible runs leave free; membership is unchanged
--   - encoding: an element in $P_Q$ remains in that list and keeps its actual level until a decrement continuation into $Q$ transfers it or an input departure removes it → every single transition (executed selected operation, or input update at a boundary) other than these two keeps it in $P_Q$, keeps $Q$ retained and keeps its level; reason: a property kept by every other transition holds until one of the two named transitions, by induction along the run; $Q$ stays retained because a deletion needs $P_Q=\emptyset$
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), Lemma 5.1, p.43 (PDF 45)

import Mathlib
import Definitions.Def_DynSetCover_Algorithm

namespace DynSetCover

/-- **Lemma 5.1 (Level bounds and protection of pending elements)** (Paul, Solomon, STOC 2027
submission, sha256 a671756b…, p.43 (PDF 45)). At every state of an admissible run of the §5
algorithm with capacity `N ≥ 2`:

1. *Level bounds.* Every retained copy `Q`, including an empty copy, satisfies
   `H(S_Q) − L ≤ q_Q ≤ h_Q ≤ H(S_Q)`; every element `e` assigned to `Q` satisfies
   `q_Q ≤ ℓ(e) ≤ h_Q ≤ b(e)`; every active element satisfies `b(e) − L ≤ ℓ(e) ≤ b(e)`; and
   `R_Q ≠ ∅` implies `q_Q < h_Q`.
2. *Pending-list structure.* At most one of `P_Q`, `R_Q` is nonempty. If `P_Q ≠ ∅` then
   `q_Q = h_Q` and `ℓ(e) = h_Q + 1 ≤ b(e)` for `e ∈ P_Q`. The sets `P_Q ∪ U_Q` over the copies
   with `P_Q ≠ ∅` are pairwise disjoint.
3. *Protection of pending elements.* An element of `P_Q` remains in that list (and `Q` remains
   retained) and keeps its actual level under every transition other than a decrement
   continuation into `Q` transferring it or an input departure removing it. Moreover,
   immediately before any selected internal operation: (a) an opening selects a batch disjoint
   from `P_Q ∪ U_Q` for every copy `Q` with `P_Q ≠ ∅`; (b) a copy selected for a starting
   increment, increment continuation, commit or deletion has no assigned element in any
   pending list.

**Formalization Note.** "Assigned to `Q`" is membership in `cov_t(Q) = U_Q ∪ R_Q`. The
transitions of clause 3 are the executed internal operations (selected, fitting the remaining
budget) and the input updates at a boundary (the phase has stopped). The hypothesis that `ce`
is a choice of cheapest sets is the paper's "fix a cheapest set `S_e`". -/
theorem lemma_5_1 (inst : Instance) (N : ℕ) (hN : 2 ≤ N) (ce : Fin inst.u → Fin inst.m)
    (hce : inst.IsCheapest ce) (s : State inst) (b : ℝ) (hs : IsState inst N ce s b) :
    -- 1. level bounds
    (∀ Q ∈ s.copies, inst.H Q.2 - (capL N : ℤ) ≤ s.q Q ∧ s.q Q ≤ s.h Q ∧ s.h Q ≤ inst.H Q.2) ∧
    (∀ Q ∈ s.copies, ∀ e ∈ cov inst s Q,
      s.q Q ≤ s.level e ∧ s.level e ≤ s.h Q ∧ s.h Q ≤ inst.base e) ∧
    (∀ e ∈ s.active, inst.base e - (capL N : ℤ) ≤ s.level e ∧ s.level e ≤ inst.base e) ∧
    (∀ Q ∈ s.copies, s.R Q ≠ ∅ → s.q Q < s.h Q) ∧
    -- 2. pending-list structure
    (∀ Q ∈ s.copies, s.P Q = ∅ ∨ s.R Q = ∅) ∧
    (∀ Q ∈ s.copies, s.P Q ≠ ∅ →
      s.q Q = s.h Q ∧ ∀ e ∈ s.P Q, s.level e = s.h Q + 1 ∧ s.h Q + 1 ≤ inst.base e) ∧
    (∀ Q ∈ s.copies, ∀ Q' ∈ s.copies, Q ≠ Q' → s.P Q ≠ ∅ → s.P Q' ≠ ∅ →
      Disjoint (s.P Q ∪ s.U Q) (s.P Q' ∪ s.U Q')) ∧
    -- 3. protection of pending elements: internal operations
    (∀ o, Selected inst N s o → charge inst N o ≤ b →
      ∀ Q ∈ s.copies, ∀ e ∈ s.P Q, o ≠ Op.decCont Q e →
        Q ∈ (exec inst s o).copies ∧ e ∈ (exec inst s o).P Q ∧
          (exec inst s o).level e = s.level e) ∧
    -- 3. protection of pending elements: input updates
    (Stops inst N s b → ∀ x, UpdateOK inst N s x →
      ∀ Q ∈ s.copies, ∀ e ∈ s.P Q, x ≠ Upd.del e →
        Q ∈ (applyUpdate inst ce s x).copies ∧ e ∈ (applyUpdate inst ce s x).P Q ∧
          (applyUpdate inst ce s x).level e = s.level e) ∧
    -- 3(a)
    (∀ S r, Selected inst N s (Op.opening S r) →
      ∀ Q ∈ s.copies, s.P Q ≠ ∅ → Disjoint (batch inst s S r) (s.P Q ∪ s.U Q)) ∧
    -- 3(b)
    (∀ o Q, Selected inst N s o → o.copyOf = some Q →
      ∀ e ∈ cov inst s Q, ∀ Q' ∈ s.copies, e ∉ s.P Q') := by sorry

end DynSetCover
