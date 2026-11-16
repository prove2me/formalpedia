-- Prove2me | Theorems.Thm_DynEdgeColorLLL_Main_Supplement_corollary_4
-- name    : DynEdgeColorLLL.Main.Supplement.corollary_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:03:46.516176+00:00
-- url     : https://prove2.me/theorems/4521542b-114c-452b-b489-c49d50a8e9f2
-- title:
--   Corollary 4 — complete transcript reconstruction at termination
-- statement:
--   Use the same truth-table family, old instance, incidence batch and shared randomness tables as for Lemma 5, starting with the completed old static transcript. Suppose the repair first stops after stage $R\ge1$, when $\mathcal C_{R+1}=\varnothing$. Then the stage invariants of Lemma 5 hold for every $r\ge1$, with the empty-stage extension, and after the specified cleanup the stored transcript equals the entire new static transcript:
--
--   $$T_{\rm stored}=T^{\rm new}.$$
--
--   Equality includes all selection sets, resampling bits, clause-falsification bits, counters, stage assignments, resampling totals, last-resampling stages, reported final values and clause last stages. The claim is conditional on termination and supplies the reconstruction guarantee used by Theorem 2.
--
--   Differences from the source:
--   - encoding: The old static transcript is stored before the repair, and recovered entries and assignments use the shared tables → FiniteOld makes the completed old static execution explicit; stored arrays and their readout are given by the repair recurrence; reason: Makes the operational precondition and every recovered quantity explicit without assuming an invariant
--   - generalization: Section 3 imposes probabilistic LLL and uniform parameter assumptions → The deterministic repair claim is stated for every truth-table family and the completed static transcripts specified here, without numerical LLL hypotheses; reason: The deterministic statement needs only truth-table locality and the actual repair recurrence, and specializes to every completed source execution
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Corollary 4, printed p. 14 (PDF p. 16)

import Definitions.Def_DynEdgeColorLLL_Main_Supplement_Repair

set_option autoImplicit false

namespace DynEdgeColorLLL.Main.Supplement

/-- Corollary 4, printed p. 14 / PDF p. 16: the empty-stage extension and full reconstruction. -/
theorem corollary_4
    {X : Type*} [Fintype X] [DecidableEq X] {Ω : X → Type*}
    [∀ x, MeasurableSpace (Ω x)] {m : ℕ}
    (f : TruthTables X Ω m) (hf : IsTruthTableFamily f)
    (old : Fin m → Finset X) (B : Finset (Fin m × X))
    (τ : (x : X) → ℕ → Ω x) (hold : FiniteOld f old τ)
    (R : ℕ) (hstop : StopsAfter f old B τ R) :
    (∀ r : ℕ, 1 ≤ r → RepairInvariants f old B τ (repairAt f old B τ (r - 1)) r) ∧
      Reconstructs f (applyBatch old B) τ (cleanupRepair f old B τ R) := by sorry

end DynEdgeColorLLL.Main.Supplement
