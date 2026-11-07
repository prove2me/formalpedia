-- Prove2me | Theorems.Thm_DynSetCover_lemma_4_2
-- name    : DynSetCover.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:46:05.23249+00:00
-- url     : https://prove2.me/theorems/f1a585da-1b62-4506-8866-b4bd6d9cfc57
-- title:
--   Lemma 4.2 — bounds and update sensitivity of $g_j$
-- statement:
--   Let $A$ be a finite set of elements and $j$ an integer, and let $g_j$ be the augmented covering optimum at scale $j$. Then
--   $$0\le g_j(A)\le\min\{|A^{\ge j}|,\ 2^{-j}\,\mathrm{OPT}(A)\}.$$
--   Moreover:
--   1. if $A^{\ge j}=\emptyset$ then $g_j(A)=0$;
--   2. an input update changes $g_j$ by at most one: $|g_j(A\cup\{e\})-g_j(A)|\le1$ for every $e\notin A$;
--   3. internal operations of the §5 algorithm leave $g_j$ unchanged, since they do not change the active set.
--
--   These bounds are used to compare the potential tails with $g_j$ before and after each input update.
--
--   **Formalization Note** Clause 2 covers both an arrival ($A\to A\cup\{e\}$) and a departure ($A\cup\{e\}\to A$).
--
--   Differences from the source:
--   - generalization: a fixed family $\mathcal F$ of subsets of $U$ whose union is $U$ → an indexed family $(S_s)_{s<m}$ of subsets of $U$ with union $U$, in which two indices may carry the same subset; reason: the paper's family is an injectively indexed one; no step of the argument uses that the sets are distinct
--   - generalization: every active set $A=A_t$; internal operations of a run → every finite set $A$ of elements; every state and every operation; reason: the bounds mention only the instance and $A$, and an operation never changes the active set
--   - encoding: an input update changes $g_j$ by at most one → $|g_j(A\cup\{e\})-g_j(A)|\le1$ for $e\notin A$; reason: an arrival of $e$ takes $A$ to $A\cup\{e\}$ and a departure takes $A\cup\{e\}$ to $A$
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), Lemma 4.2, p.26 (PDF 28)

import Mathlib
import Definitions.Def_DynSetCover_Rounding
import Definitions.Def_DynSetCover_Algorithm

namespace DynSetCover

/-- **Lemma 4.2 (Bounds and update sensitivity of `g_j`)** (Paul, Solomon, STOC 2027
submission, sha256 a671756b…, p.26 (PDF 28)). For every finite set `A` of elements and every
integer `j`: `0 ≤ g_j(A) ≤ min{|A^{≥j}|, 2^{−j} OPT(A)}`; if `A^{≥j} = ∅` then `g_j(A) = 0`;
an input update (inserting an element `e ∉ A`, or equivalently deleting it from `insert e A`)
changes `g_j` by at most one; internal operations leave it unchanged.

**Formalization Note.** The paper states the lemma for `A = A_t`; it mentions only the instance
and `A`, so it is stated for every `A`. Internal operations leave `g_j` unchanged because they do
not change the active set; the last clause states this for every state and operation. -/
theorem lemma_4_2 (inst : Instance) (A : Finset (Fin inst.u)) (j : ℤ) :
    0 ≤ inst.g j A ∧ inst.g j A ≤ ((inst.above A j).card : ℝ) ∧
    inst.g j A ≤ (2 : ℝ) ^ (-j) * inst.OPT A ∧
    (inst.above A j = ∅ → inst.g j A = 0) ∧
    (∀ e ∉ A, |inst.g j (insert e A) - inst.g j A| ≤ 1) ∧
    (∀ (s : State inst) (o : Op inst), inst.g j (exec inst s o).active = inst.g j s.active) := by sorry

end DynSetCover
