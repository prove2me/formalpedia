-- Prove2me | Theorems.Thm_DynSetCover_corollary_6_8
-- name    : DynSetCover.corollary_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:48:12.192978+00:00
-- url     : https://prove2.me/theorems/570987e8-2459-4c1b-9415-8bc074b3882c
-- title:
--   Corollary 6.8 — $1024(1+\ln\Delta_t)$-approximation at every update boundary
-- statement:
--   Throughout, the states and update boundaries are those of admissible runs of the faster algorithm of §5 with capacity $N\ge2$ on valid update sequences keeping $|A_t|\le N$, with $L=\lceil\log_2(2N)\rceil$ and $\eta=1/L$.
--
--   At every update boundary $t$ with $A_t\neq\emptyset$,
--   $$\sum_{S:\ \mu_t(S)>0}c_0(S)\le1024\,(1+\ln\Delta_t)\,\mathrm{OPT}_0(A_t),\qquad\Delta_t=\max_{S\in\mathcal F}|S\cap A_t|.$$
--   If $A_t=\emptyset$, no copy remains retained and the maintained (physical) cover is empty.
--
--   This is the approximation guarantee of the faster algorithm with a known capacity.
--
--   Differences from the source:
--   - generalization: a fixed family $\mathcal F$ of subsets of $U$ whose union is $U$ → an indexed family $(S_s)_{s<m}$ of subsets of $U$ with union $U$, in which two indices may carry the same subset; reason: the paper's family is an injectively indexed one; no step of the argument uses that the sets are distinct
--   - generalization: the run of the §5 algorithm with FIFO tie-breaking inside each priority and category, continuations moving the head element of a list, and one fixed cheapest set $S_e$ per element → every admissible run: any operation that is applicable and maximal in (priority, category order), any element of the list, and any choice of cheapest sets; reason: no proof in §§5–6 uses the FIFO or head-element rules or the particular cheapest set; the paper's run is one admissible run
--   - encoding: the lists $U_Q$, $R_Q$, $P_Q$ → finite sets of elements; reason: list order serves only the tie-breaking and head-element choices that the admissible runs leave free; membership is unchanged
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), Corollary 6.8, p.55 (PDF 57)

import Mathlib
import Definitions.Def_DynSetCover_Potential

namespace DynSetCover

/-- **Corollary 6.8** (Paul, Solomon, STOC 2027 submission, sha256 a671756b…, p.55 (PDF 57)).
At every update boundary `t` with `A_t ≠ ∅`,
`Σ_{S: µ_t(S)>0} c0(S) ≤ 1024(1 + ln Δ_t) OPT0(A_t)`, where `Δ_t = max_{S∈F} |S ∩ A_t|`. If
`A_t = ∅`, no copy remains retained, and the maintained cover is empty.

**Formalization Note.** Update boundaries are those of admissible runs of the §5 algorithm with
capacity `N ≥ 2`; the maintained cover is `physCover`. -/
theorem corollary_6_8 (inst : Instance) (N : ℕ) (hN : 2 ≤ N) (ce : Fin inst.u → Fin inst.m)
    (hce : inst.IsCheapest ce) (s : State inst) (hs : IsBoundary inst N ce s) :
    (s.active.Nonempty →
      inst.cost0 (physCover inst s) ≤
        1024 * (1 + Real.log (inst.maxLoad s.active : ℝ)) * inst.OPT0 s.active) ∧
    (s.active = ∅ → s.copies = ∅ ∧ physCover inst s = ∅) := by sorry

end DynSetCover
