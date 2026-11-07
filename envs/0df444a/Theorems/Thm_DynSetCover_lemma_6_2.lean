-- Prove2me | Theorems.Thm_DynSetCover_lemma_6_2
-- name    : DynSetCover.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:47:00.891419+00:00
-- url     : https://prove2.me/theorems/895fc08e-0539-43ed-899c-7cfb0cbd8e1e
-- title:
--   Lemma 6.2 — an arrival raises $\Phi$ and every $\Phi_i$ by at most $26$; a departure raises none
-- statement:
--   Throughout, the states and update boundaries are those of admissible runs of the faster algorithm of §5 with capacity $N\ge2$ on valid update sequences keeping $|A_t|\le N$, with $L=\lceil\log_2(2N)\rceil$ and $\eta=1/L$.
--
--   Let $s$ be an update boundary and $s'$ the state right after the next input update (before any internal operation). If the update is an arrival, then
--   $$\Phi(s')\le\Phi(s)+26\quad\text{and}\quad\Phi_i(s')\le\Phi_i(s)+26\ \text{ for every integer } i.$$
--   If it is a departure, then $\Phi(s')\le\Phi(s)$ and $\Phi_i(s')\le\Phi_i(s)$ for every $i$.
--
--   This bounds the excess that the repair phase after one update has to remove.
--
--   Differences from the source:
--   - generalization: a fixed family $\mathcal F$ of subsets of $U$ whose union is $U$ → an indexed family $(S_s)_{s<m}$ of subsets of $U$ with union $U$, in which two indices may carry the same subset; reason: the paper's family is an injectively indexed one; no step of the argument uses that the sets are distinct
--   - generalization: the run of the §5 algorithm with FIFO tie-breaking inside each priority and category, continuations moving the head element of a list, and one fixed cheapest set $S_e$ per element → every admissible run: any operation that is applicable and maximal in (priority, category order), any element of the list, and any choice of cheapest sets; reason: no proof in §§5–6 uses the FIFO or head-element rules or the particular cheapest set; the paper's run is one admissible run
--   - encoding: the lists $U_Q$, $R_Q$, $P_Q$ → finite sets of elements; reason: list order serves only the tie-breaking and head-element choices that the admissible runs leave free; membership is unchanged
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), Lemma 6.2, p.49 (PDF 51)

import Mathlib
import Definitions.Def_DynSetCover_Potential

namespace DynSetCover

/-- **Lemma 6.2 (Changes caused by input updates)** (Paul, Solomon, STOC 2027 submission,
sha256 a671756b…, p.49 (PDF 51)). An arrival increases `Φ` and every `Φ_i` by at most `26`.
A departure cannot increase `Φ` or any `Φ_i`.

**Formalization Note.** Input updates are applied at update boundaries of admissible runs with
capacity `N ≥ 2`. -/
theorem lemma_6_2 (inst : Instance) (N : ℕ) (hN : 2 ≤ N) (ce : Fin inst.u → Fin inst.m)
    (hce : inst.IsCheapest ce) (s : State inst) (hs : IsBoundary inst N ce s)
    (x : Upd inst.u) (hx : UpdateOK inst N s x) :
    (∀ e, x = Upd.ins e →
      Phi inst N (applyUpdate inst ce s x) ≤ Phi inst N s + 26 ∧
      ∀ i : ℤ, PhiTail inst N (applyUpdate inst ce s x) i ≤ PhiTail inst N s i + 26) ∧
    (∀ e, x = Upd.del e →
      Phi inst N (applyUpdate inst ce s x) ≤ Phi inst N s ∧
      ∀ i : ℤ, PhiTail inst N (applyUpdate inst ce s x) i ≤ PhiTail inst N s i) := by sorry

end DynSetCover
