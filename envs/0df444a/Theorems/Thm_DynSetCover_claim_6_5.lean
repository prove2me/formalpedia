-- Prove2me | Theorems.Thm_DynSetCover_claim_6_5
-- name    : DynSetCover.claim_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:47:08.428791+00:00
-- url     : https://prove2.me/theorems/b110648b-93cf-4ca1-9880-8eb4f17872c3
-- title:
--   Claim 6.5 — $\Phi_i\le 464\,g_i(A)$ in a state clean at $i$
-- statement:
--   Throughout, the states and update boundaries are those of admissible runs of the faster algorithm of §5 with capacity $N\ge2$ on valid update sequences keeping $|A_t|\le N$, with $L=\lceil\log_2(2N)\rceil$ and $\eta=1/L$.
--
--   If a state with active set $A$ is clean at the integer cutoff $i$ (no applicable operation has priority at least $i$), then
--   $$\Phi_i\le 464\,g_i(A).$$
--
--   This is the first case of the cutoff certificate (Lemma 6.4).
--
--   Differences from the source:
--   - generalization: a fixed family $\mathcal F$ of subsets of $U$ whose union is $U$ → an indexed family $(S_s)_{s<m}$ of subsets of $U$ with union $U$, in which two indices may carry the same subset; reason: the paper's family is an injectively indexed one; no step of the argument uses that the sets are distinct
--   - generalization: the run of the §5 algorithm with FIFO tie-breaking inside each priority and category, continuations moving the head element of a list, and one fixed cheapest set $S_e$ per element → every admissible run: any operation that is applicable and maximal in (priority, category order), any element of the list, and any choice of cheapest sets; reason: no proof in §§5–6 uses the FIFO or head-element rules or the particular cheapest set; the paper's run is one admissible run
--   - encoding: the lists $U_Q$, $R_Q$, $P_Q$ → finite sets of elements; reason: list order serves only the tie-breaking and head-element choices that the admissible runs leave free; membership is unchanged
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), Claim 6.5, p.52 (PDF 54)

import Mathlib
import Definitions.Def_DynSetCover_Potential

namespace DynSetCover

/-- **Claim 6.5** (Paul, Solomon, STOC 2027 submission, sha256 a671756b…, p.52 (PDF 54)). If
the state is clean at `i`, then `Φ_i ≤ 464 g_i(A)`.

**Formalization Note.** States are those of admissible runs with capacity `N ≥ 2`; `A` is the
state's active set. -/
theorem claim_6_5 (inst : Instance) (N : ℕ) (hN : 2 ≤ N) (ce : Fin inst.u → Fin inst.m)
    (hce : inst.IsCheapest ce) (s : State inst) (b : ℝ) (hs : IsState inst N ce s b) (i : ℤ)
    (hclean : CleanAt inst N s i) :
    PhiTail inst N s i ≤ 464 * inst.g i s.active := by sorry

end DynSetCover
