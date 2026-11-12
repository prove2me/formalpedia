-- Prove2me | Theorems.Thm_DynEdgeColorLLL_Main_lemma_4
-- name    : DynEdgeColorLLL.Main.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:34.88548+00:00
-- url     : https://prove2.me/theorems/f3ce219e-6f4a-48ad-9754-2d42103fec3b
-- title:
--   Lemma 4 — every dirty pair $(C,r)$ has $\mathrm{dist}_{H^\cup}(C,\mathcal M)\le 2r-1$
-- statement:
--   Let a batch $B$ of distinct clause updates turn the variable sets $\mathrm{vbl}^{old}$ into $\mathrm{vbl}^{new}$. The update $(C_i,x_i)$ adds $x_i$ to $\mathrm{vbl}(C_i)$ when $x_i\notin\mathrm{vbl}(C_i)$ and removes it otherwise. Let $\mathcal M=\{C_i\}$ be the updated clauses and $H^\cup=H^{old}\cup H^{new}$. Run the static transcripts of both instances on the same randomness tables $R$. Then for every $r\ge1$, every dirty pair $(C,r)$ (one where $(b^{old}_{C,r},\mathrm{cnt}^{old}_{C,r})\ne(b^{new}_{C,r},\mathrm{cnt}^{new}_{C,r})$) satisfies
--   $$\mathrm{dist}_{H^\cup}(C,\mathcal M)\le 2r-1 .$$
--
--   The statement is deterministic: it holds for every realization of the randomness tables. It localizes the effect of a batch, and the expected-recourse bound of Corollary 3 rests on it.
--
--   **Formalization Note.** The distance bound is the existence of a clause $C'\in\mathcal M$ and a walk of length at most $2r-1$ from $C$ to $C'$ in $H^\cup$.
--
--   Differences from the source:
--   - encoding: a set V of variables and clause IDs in [m] → a finite type of variables and clause IDs Fin m; reason: every instance in the paper is finite at every moment
--   - generalization: stated under the standing assumptions of §3.1 (parameters k, s, d, q and assumption (1)) → no parameter bound or assumption (1) is assumed; only the truth-table conventions (locality, empty clauses satisfied, measurability); reason: the lemma is deterministic and its proof uses none of them, so the Lean statement specializes to the source
--   - encoding: a truth table f_{C,U} : ∏_{x∈U} Ω_x → {0,1} for each clause C and variable set U → a predicate f C U on full assignments that depends only on the coordinates in U, is false for U = ∅, and has a measurable falsifying set (IsTruthTableFamily); reason: the same truth tables; the empty-clause convention is stated in §3.1, and measurability is presupposed by Pr[C] in assumption (1)
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Lemma 4, printed p. 12 (PDF p. 14); batches and dirty pairs §3.3, printed p. 11 (PDF p. 13)

import Mathlib
import Definitions.Def_DynEdgeColorLLL_Main_LLLTranscript
open MeasureTheory
open scoped ENNReal

namespace DynEdgeColorLLL.Main

/-- Lemma 4 (Peng–Ghaffari, STOC 2027 submission #615, printed p. 12, PDF p. 14). Let the new
instance arise from the old one by a batch `B` of distinct clause updates, and run both static
transcripts on the same randomness table `τ`. Every dirty pair `(C, r)` satisfies
`dist_{H^∪}(C, M) ≤ 2r − 1`, where `M` is the set of updated clauses. -/
theorem lemma_4 {X : Type*} [Fintype X] [DecidableEq X] {Ω : X → Type*}
    [∀ x, MeasurableSpace (Ω x)] {m : ℕ} (f : TruthTables X Ω m) (vbl : Fin m → Finset X)
    (B : Finset (Fin m × X)) (hf : IsTruthTableFamily f) (τ : (x : X) → ℕ → Ω x)
    (C : Fin m) (r : ℕ) (hr : 1 ≤ r) (hdirty : IsDirty f vbl (applyBatch vbl B) τ C r) :
    ∃ C' ∈ touched B, ∃ p : (unionDepGraph vbl (applyBatch vbl B)).Walk C C',
      p.length ≤ 2 * r - 1 := by sorry

end DynEdgeColorLLL.Main
