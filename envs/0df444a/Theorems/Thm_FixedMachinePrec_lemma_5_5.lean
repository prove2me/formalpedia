-- Prove2me | Theorems.Thm_FixedMachinePrec_lemma_5_5
-- name    : FixedMachinePrec.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:06:53.226732+00:00
-- url     : https://prove2.me/theorems/14bb5c0c-64b4-47f5-9c20-d5c07b7abaf6
-- title:
--   Lemma 5.5 — one pass finds exactly the reachable states
-- statement:
--   Let $m\ge1$, let $\prec$ be a strict partial order on $J$, let $W\subseteq J$, let $\mathcal F_{\mathrm{cut}}$ be a cut family, and let $S_W=(L_i,Z_i,R_i)_{i<s}$ be the state list of $W$ built by Algorithm 3. Fix the lookup answers (the table does not change while $W$ is processed). After Steps 3–4 of Algorithm 4:
--
--   1. a record $j$ is marked if and only if some initial record $i$ (with $\mathrm{Lookup}(L_i)=1$) reaches $j$ along edges (2);
--   2. for a marked record $j$, following its predecessor fields back to START yields a path $i_1,\dots,i_k=j$ along edges (2) whose first record is initial with predecessor START.
--
--   **Formalization Note** Record indices are $0$-based. The statement holds for every fixed lookup function; Algorithm 4 uses the answers of its current table.
--
--   Differences from the source:
--   - generalization: the scope m ≥ 3 of the explicit procedures (p.1) → every m ≥ 1; reason: the proof uses only |L_j| ≥ |L_i| + m > |L_i|, which needs m ≥ 1; m ≥ 3 is a case
--   - generalization: the lookup answers of Algorithm 4's table while W is processed → an arbitrary fixed lookup function lk; reason: the proof uses only that the edge relation is fixed; the table's answers are one such function
--   - encoding: record indices 1, …, s → 0, …, s − 1; reason: Lean convention
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Lemma 5.5, p.14

import Mathlib
import Definitions.Def_FixedMachinePrec_EvaluateFamily

namespace FixedMachinePrec

/-- **Lemma 5.5 (The pass computes exactly the reachable states).** Jansen, *Precedence Constraint
Scheduling on a Fixed Number of Machines* (manuscript, sha256 08cdf3e1…), Lemma 5.5, p.14: "At the
end of Step 4 of Algorithm 4, a record is marked exactly when it is reachable from an initial
record by edges (2). Its predecessor fields describe such a path."

Let `st = S_W` be the state list built by Algorithm 3 for a parent `W` and a cut family `F_cut`,
and fix the lookup answers `lk` (the table does not change while `W` is processed). After the pass
of Steps 3–4, with `s = |S_W|`:
1. a record `j < s` is marked iff some initial record `i` (`Lookup(L_i) = 1`) reaches `j` along
   edges (2);
2. for a marked `j`, following its predecessor fields back to `START` gives a nonempty path that
   starts at an initial record with predecessor `START`, ends at `j`, and follows edges (2).

**Formalization Note** Record indices are 0-based. The statement is made for every lookup function
`lk`; Algorithm 4 uses `lk X = (Lookup(X) = 1)` on its current table. The predecessor path is
traced with at most `s` records (`tracePath`, as in Algorithm 5). -/
theorem lemma_5_5 {N : ℕ} (m : ℕ) (hm : 1 ≤ m) (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (hprec : IsStrictOrder' prec) (Fcut : Finset (Finset (Fin N))) (W : Finset (Fin N))
    (lk : Finset (Fin N) → Bool) :
    let st := buildStates prec m Fcut W
    let E : ℕ → ℕ → Prop := fun i j => edge st lk i j = true
    let initial : ℕ → Prop := fun i => ∃ a, st[i]? = some a ∧ lk a.L = true
    (∀ j < st.length,
      ((reachPass st lk).1 j = true ↔ ∃ i, initial i ∧ Relation.ReflTransGen E i j)) ∧
    (∀ j < st.length, (reachPass st lk).1 j = true →
      let path := tracePath (reachPass st lk).2 st.length j
      ∃ i₁ rest, path = i₁ :: rest ∧ initial i₁ ∧ (reachPass st lk).2 i₁ = .start ∧
        path.getLast? = some j ∧ path.IsChain E) := by sorry

end FixedMachinePrec
