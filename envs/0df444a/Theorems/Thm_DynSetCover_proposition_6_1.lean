-- Prove2me | Theorems.Thm_DynSetCover_proposition_6_1
-- name    : DynSetCover.proposition_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:47:51.826909+00:00
-- url     : https://prove2.me/theorems/03cb4da6-492f-4e0c-9050-6ecb0df8ca0a
-- title:
--   Proposition 6.1 — reduction to retained cost
-- statement:
--   Throughout, the states and update boundaries are those of admissible runs of the faster algorithm of §5 with capacity $N\ge2$ on valid update sequences keeping $|A_t|\le N$, with $L=\lceil\log_2(2N)\rceil$ and $\eta=1/L$.
--
--   Let $t$ be an update boundary and $K$ a real number such that
--   $$N_i\le K\,g_i(A_t)\qquad\text{for every integer } i.\tag{38}$$
--   If $A_t\neq\emptyset$, the physical cover satisfies
--   $$\sum_{S:\ \mu_t(S)>0}c_0(S)\le 2K\,(1+\ln\Delta_t)\,\mathrm{OPT}_0(A_t),\qquad\Delta_t=\max_{S\in\mathcal F}|S\cap A_t|.$$
--   If $A_t=\emptyset$, no copy remains retained.
--
--   This is the reduction of the approximation ratio to a scale-by-scale bound on the normalized retained costs.
--
--   Differences from the source:
--   - generalization: a fixed family $\mathcal F$ of subsets of $U$ whose union is $U$ → an indexed family $(S_s)_{s<m}$ of subsets of $U$ with union $U$, in which two indices may carry the same subset; reason: the paper's family is an injectively indexed one; no step of the argument uses that the sets are distinct
--   - generalization: the run of the §5 algorithm with FIFO tie-breaking inside each priority and category, continuations moving the head element of a list, and one fixed cheapest set $S_e$ per element → every admissible run: any operation that is applicable and maximal in (priority, category order), any element of the list, and any choice of cheapest sets; reason: no proof in §§5–6 uses the FIFO or head-element rules or the particular cheapest set; the paper's run is one admissible run
--   - encoding: the lists $U_Q$, $R_Q$, $P_Q$ → finite sets of elements; reason: list order serves only the tie-breaking and head-element choices that the admissible runs leave free; membership is unchanged
--   - generalization: an absolute constant $K$ → any real number $K$; reason: the statement is the same for each value of $K$; an absolute constant is one such value
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), Proposition 6.1, p.46 (PDF 48)

import Mathlib
import Definitions.Def_DynSetCover_Potential

namespace DynSetCover

/-- **Proposition 6.1 (Reduction to retained cost)** (Paul, Solomon, STOC 2027 submission,
sha256 a671756b…, p.46 (PDF 48)). Suppose that, at an update boundary `t`, a constant `K`
satisfies `N_i ≤ K g_i(A_t)` for every integer `i` (38). If `A_t ≠ ∅`, then
`Σ_{S: µ_t(S)>0} c0(S) ≤ 2K(1 + ln Δ_t) OPT0(A_t)`. If `A_t = ∅`, no copy remains retained.

**Formalization Note.** `K` is any real number. The physical cover `{S : µ_t(S) > 0}` is
`physCover`, and `Δ_t = maxLoad A_t`. -/
theorem proposition_6_1 (inst : Instance) (N : ℕ) (hN : 2 ≤ N) (ce : Fin inst.u → Fin inst.m)
    (hce : inst.IsCheapest ce) (s : State inst) (hs : IsBoundary inst N ce s) (K : ℝ)
    (hK : ∀ i : ℤ, Ntail inst s i ≤ K * inst.g i s.active) :
    (s.active.Nonempty →
      inst.cost0 (physCover inst s) ≤
        2 * K * (1 + Real.log (inst.maxLoad s.active : ℝ)) * inst.OPT0 s.active) ∧
    (s.active = ∅ → s.copies = ∅) := by sorry

end DynSetCover
