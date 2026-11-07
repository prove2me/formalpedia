-- Prove2me | Theorems.Thm_DynSetCover_proposition_6_7
-- name    : DynSetCover.proposition_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:47:27.808352+00:00
-- url     : https://prove2.me/theorems/22345fa3-1232-45b4-aff0-8dd702d00ca0
-- title:
--   Proposition 6.7 — boundary invariant $0\le\Phi_i\le1024\,g_i(A_t)$ and $N_i\le512\,g_i(A_t)$
-- statement:
--   Throughout, the states and update boundaries are those of admissible runs of the faster algorithm of §5 with capacity $N\ge2$ on valid update sequences keeping $|A_t|\le N$, with $L=\lceil\log_2(2N)\rceil$ and $\eta=1/L$.
--
--   At every update boundary $t$ and every integer cutoff $i$,
--   $$0\le\Phi_i\le1024\,g_i(A_t),\tag{46}$$
--   and consequently
--   $$N_i\le512\,g_i(A_t).$$
--
--   This is the retained-cost bound (38) with $K=512$ that Proposition 6.1 turns into the approximation ratio.
--
--   Differences from the source:
--   - generalization: a fixed family $\mathcal F$ of subsets of $U$ whose union is $U$ → an indexed family $(S_s)_{s<m}$ of subsets of $U$ with union $U$, in which two indices may carry the same subset; reason: the paper's family is an injectively indexed one; no step of the argument uses that the sets are distinct
--   - generalization: the run of the §5 algorithm with FIFO tie-breaking inside each priority and category, continuations moving the head element of a list, and one fixed cheapest set $S_e$ per element → every admissible run: any operation that is applicable and maximal in (priority, category order), any element of the list, and any choice of cheapest sets; reason: no proof in §§5–6 uses the FIFO or head-element rules or the particular cheapest set; the paper's run is one admissible run
--   - encoding: the lists $U_Q$, $R_Q$, $P_Q$ → finite sets of elements; reason: list order serves only the tie-breaking and head-element choices that the admissible runs leave free; membership is unchanged
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), Proposition 6.7, p.54 (PDF 56)

import Mathlib
import Definitions.Def_DynSetCover_Potential

namespace DynSetCover

/-- **Proposition 6.7 (Boundary invariant)** (Paul, Solomon, STOC 2027 submission, sha256
a671756b…, p.54 (PDF 56)). At every update boundary `t` and every integer cutoff `i`,
`0 ≤ Φ_i ≤ 1024 g_i(A_t)` (46). Consequently, `N_i ≤ 512 g_i(A_t)`.

**Formalization Note.** Update boundaries are those of admissible runs with capacity `N ≥ 2` on
valid update sequences with `|A_t| ≤ N` throughout (`IsBoundary`); `A_t` is the boundary
state's active set. -/
theorem proposition_6_7 (inst : Instance) (N : ℕ) (hN : 2 ≤ N) (ce : Fin inst.u → Fin inst.m)
    (hce : inst.IsCheapest ce) (s : State inst) (hs : IsBoundary inst N ce s) (i : ℤ) :
    0 ≤ PhiTail inst N s i ∧ PhiTail inst N s i ≤ 1024 * inst.g i s.active ∧
    Ntail inst s i ≤ 512 * inst.g i s.active := by sorry

end DynSetCover
