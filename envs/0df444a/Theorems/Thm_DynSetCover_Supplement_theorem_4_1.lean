-- Prove2me | Theorems.Thm_DynSetCover_Supplement_theorem_4_1
-- name    : DynSetCover.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:57:16.482249+00:00
-- url     : https://prove2.me/theorems/b132017c-7906-4b83-abf5-a3c368a14326
-- title:
--   Theorem 4.1 — the §3 batch algorithm is $2048(1+\ln\Delta_t)$-approximate at every update boundary
-- statement:
--   Consider the batch algorithm of §3 (rounded costs $c(S)=2^{\lceil\log_2 c_0(S)\rceil}$, geometric volume $\mathrm{vol}(e,i)=2^{i-b(e)}$, level decrements, level increments and empty-copy deletions selected by maximum priority, at most $2048$ internal operations per update). Write $A_t$ for the active set at update boundary $t$, $\mu_t(S)$ for the number of retained copies of the input set $S$, and $\Delta_t=\max_{S\in\mathcal F}|S\cap A_t|$.
--
--   At every update boundary with $A_t\neq\emptyset$,
--   $$\sum_{S:\ \mu_t(S)>0}c_0(S)\le2048\,(1+\ln\Delta_t)\,\mathrm{OPT}_0(A_t).$$
--   If $A_t=\emptyset$, no copy remains retained and the maintained (physical) cover is empty.
--
--   The bound holds at every update boundary, even when further decrements, increments or deletions remain applicable; it is the approximation guarantee behind Theorem 1.1.
--
--   **Formalization Note** The sum runs over the physical cover, each input set with at least one retained copy counted once, with original costs. Runs are quantified over every admissible tie-breaking and every choice of cheapest sets.
--
--   Differences from the source:
--   - generalization: a fixed family $\mathcal F$ of subsets of $U$ whose union is $U$ → an indexed family $(S_s)_{s<m}$ of subsets of $U$ with union $U$, in which two indices may carry the same subset; reason: the paper's family is an injectively indexed one; no step of the argument uses that the sets are distinct
--   - generalization: the run of the §3 batch algorithm with FIFO tie-breaking within each priority class (and a fixed deterministic order for simultaneous ties), and one fixed cheapest set $S_e$ per element → every admissible run: each executed operation applicable and maximal in (priority, decrement-first) order, at most $2048$ operations per update, stopping earlier only when none is applicable; any choice of cheapest (rounded-cost) sets $S_e$; reason: the proof in §4 (pp.24–38) never uses the FIFO rule or the particular cheapest set; the paper's run is one admissible run
--   - encoding: the actual level $\ell(e)=h_{\phi_t(e)}$ → a stored level function, updated together with $h_Q$ by every operation that moves elements; reason: the update rules keep $\ell(e)=h_Q$ for every $e\in\mathrm{cov}_t(Q)$, so the stored level is the paper's $\ell$ on active elements
--   - encoding: at every update boundary → for every update $t$ with $1\le t\le|\sigma|$, the boundary state $bs_t$ of an admissible run on $\sigma$ from the initial empty state; its active set is $A_t$; reason: an update boundary is the state reached after an update and its repair phase (p.21)
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), Theorem 4.1, p.24 (PDF 26); algorithm §3.1.3, pp.17–21 (PDF 19–23)

import Mathlib
import Definitions.Def_DynSetCover_Supplement_BatchAlgorithm

namespace DynSetCover.Supplement

/-- **Theorem 4.1 (Approximation at update boundaries)** (Paul, Solomon, *Weighted Set Cover with
Constant Worst-Case Recourse*, STOC 2027 submission, sha256 a671756b…, p.24 (PDF 26)). At every
update boundary of the batch algorithm of §3 with `A_t ≠ ∅`,
`Σ_{S : µ_t(S) > 0} c0(S) ≤ 2048(1 + ln Δ_t) OPT0(A_t)`, where `Δ_t = max_{S∈F} |S ∩ A_t|`. If
`A_t = ∅`, no copy remains retained and the maintained cover is empty.

For every instance, every choice `ce` of cheapest (rounded-cost) sets, every update sequence
`σ` and every admissible run `bs` of the batch algorithm on `σ`, and every update `t`
(`1 ≤ t ≤ |σ|`), the update boundary `bs t` with active set `A_t` satisfies both clauses.

**Formalization Note.** The run is any admissible run (`IsBatchRun`): every executed operation
is applicable and maximal in (priority, decrement-first) order, at most `2048` operations per
update, stopping earlier only when none is applicable; the paper's FIFO tie-breaking is one
such run. The sum is over the physical cover `physCover`, each input set with a retained copy
counted once, with original costs `c0`. `ln` is `Real.log`; `Δ_t ≥ 1` whenever `A_t ≠ ∅`. The
update boundary's active set `(bs t).active` is `A_t`. -/
theorem theorem_4_1 (inst : Instance) (ce : Fin inst.u → Fin inst.m) (hce : inst.IsCheapest ce)
    (σ : List (Upd inst.u)) (bs : ℕ → BatchState inst) (hrun : IsBatchRun inst ce σ bs)
    (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ σ.length) :
    ((bs t).active.Nonempty →
      inst.cost0 (BatchState.physCover inst (bs t)) ≤
        2048 * (1 + Real.log (inst.maxLoad (bs t).active : ℝ)) * inst.OPT0 (bs t).active) ∧
    ((bs t).active = ∅ → (bs t).copies = ∅ ∧ BatchState.physCover inst (bs t) = ∅) := by sorry

end DynSetCover.Supplement
