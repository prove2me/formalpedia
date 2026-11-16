-- Prove2me | Theorems.Thm_DynEdgeColorLLL_Main_Supplement_lemma_6
-- name    : DynEdgeColorLLL.Main.Supplement.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:04:14.350201+00:00
-- url     : https://prove2.me/theorems/53e05135-8d31-47cd-80cb-a3f287e883dd
-- title:
--   Lemma 6 — locality and late activity of every repair candidate
-- statement:
--   Fix a batch $\mathcal B$ and the old and new completed static transcripts using the same randomness tables. Let $\mathcal M$ be the clauses touched by the batch and let $H^\cup$ be the union of the old and new dependency graphs. For each $r\ge1$ and every $C\in\overline{\mathcal C}_{r+1}$ produced by the actual repair,
--
--   $$\operatorname{dist}_{H^\cup}(C,\mathcal M)\le2r,\qquad
--   \max(\ell_C^\star,\ell_C^{\rm new})\ge r.$$
--
--   Here $\ell_C^\star$ uses old last-resampling stages over the union of the old and new variable sets, and $\ell_C^{\rm new}$ is the last stage affecting a new variable of $C$. The first conclusion is represented by an actual walk of length at most $2r$ to a touched clause, which also excludes disconnected pairs. Both conclusions apply to the bar-candidate set itself. They connect the inspected region to late resampling activity for the expected-work bound.
--
--   Differences from the source:
--   - encoding: The old static transcript is stored before the repair, and recovered entries and assignments use the shared tables → FiniteOld makes the completed old static execution explicit; stored arrays and their readout are given by the repair recurrence; reason: Makes the operational precondition and every recovered quantity explicit without assuming an invariant
--   - encoding: Distance from C to the touched-clause set is at most 2r → There is a touched clause D and a walk from C to D of length at most 2r; reason: Equivalent graph-distance formulation that cannot assign a default finite distance to disconnected vertices or the empty target set
--   - reading: The two static transcripts are compared after the static algorithm has terminated almost surely; the proof uses the final satisfying new assignment → The deterministic statement explicitly assumes that both static executions finish, without assuming termination of the repair; reason: The last-activity conclusion need not hold on an exceptional nonterminating static tape; §3.2 gives termination almost surely, so every source instance is recovered almost surely
--   - generalization: Section 3 imposes probabilistic LLL and uniform parameter assumptions → The deterministic repair claim is stated for every truth-table family and the completed static transcripts specified here, without numerical LLL hypotheses; reason: The deterministic statement needs only truth-table locality and the actual repair recurrence, and specializes to every completed source execution
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Lemma 6, printed p. 16 (PDF p. 18)

import Definitions.Def_DynEdgeColorLLL_Main_Supplement_Repair

set_option autoImplicit false

namespace DynEdgeColorLLL.Main.Supplement

/-- Lemma 6, printed p. 16 / PDF p. 18: locality and late resampling for every bar candidate. -/
theorem lemma_6
    {X : Type*} [Fintype X] [DecidableEq X] {Ω : X → Type*}
    [∀ x, MeasurableSpace (Ω x)] {m : ℕ}
    (f : TruthTables X Ω m) (hf : IsTruthTableFamily f)
    (old : Fin m → Finset X) (B : Finset (Fin m × X))
    (τ : (x : X) → ℕ → Ω x) (hold : FiniteOld f old τ)
    (hnew : FiniteOld f (applyBatch old B) τ)
    (r : ℕ) (hr : 1 ≤ r) (C : Fin m)
    (hC : C ∈ (repairAt f old B τ r).previousBar) :
    (∃ D ∈ touched B, ∃ p : (unionDepGraph old (applyBatch old B)).Walk C D,
      p.length ≤ 2 * r) ∧
    (r : ℕ∞) ≤ max (starLast f old (applyBatch old B) τ C)
      (clauseLast (applyBatch old B) (rx f (applyBatch old B) τ) C) := by sorry

end DynEdgeColorLLL.Main.Supplement
