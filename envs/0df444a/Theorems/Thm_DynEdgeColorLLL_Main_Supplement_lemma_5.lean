-- Prove2me | Theorems.Thm_DynEdgeColorLLL_Main_Supplement_lemma_5
-- name    : DynEdgeColorLLL.Main.Supplement.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:03:08.129995+00:00
-- url     : https://prove2.me/theorems/55773368-f166-44b1-9103-fa961315172d
-- title:
--   Lemma 5 — all three transcript-repair invariants
-- statement:
--   Fix a truth-table family and a batch of distinct clause–variable toggles, with a completed old static transcript and shared randomness tables. Run the initialization of §3.4 and the five-step repair of §3.3. Before each stage $r\ge1$:
--
--   1. All selection sets $I_j^{\rm new}$ and resampling bits $b_{x,j}^{\rm new}$ for $1\le j<r$, and assignments $\sigma_j^{\rm new}$ for $0\le j<r$, have been recovered.
--   2. Every clause whose stage-$r$ falsification bit or counter differs between old and new transcripts belongs to $\mathcal C_r$.
--   3. The falsification bits and counters have been recovered for every clause and every $1\le j\le r$.
--
--   Thus the stored state satisfies
--
--   $$\operatorname{RepairInvariants}(r).$$
--
--   The recurrence includes the paper's extension by empty stages after stopping. This invariant describes the actual recovered entries needed for the correctness of the dynamic solver.
--
--   Differences from the source:
--   - encoding: The old static transcript is stored before the repair, and recovered entries and assignments use the shared tables → FiniteOld makes the completed old static execution explicit; stored arrays and their readout are given by the repair recurrence; reason: Makes the operational precondition and every recovered quantity explicit without assuming an invariant
--   - generalization: Section 3 imposes probabilistic LLL and uniform parameter assumptions → The deterministic repair claim is stated for every truth-table family and the completed static transcripts specified here, without numerical LLL hypotheses; reason: The deterministic statement needs only truth-table locality and the actual repair recurrence, and specializes to every completed source execution
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Lemma 5, printed p. 13 (PDF p. 15)

import Definitions.Def_DynEdgeColorLLL_Main_Supplement_Repair

set_option autoImplicit false

namespace DynEdgeColorLLL.Main.Supplement

/-- Lemma 5, printed p. 13 / PDF p. 15: all three invariants before every stage. -/
theorem lemma_5
    {X : Type*} [Fintype X] [DecidableEq X] {Ω : X → Type*}
    [∀ x, MeasurableSpace (Ω x)] {m : ℕ}
    (f : TruthTables X Ω m) (hf : IsTruthTableFamily f)
    (old : Fin m → Finset X) (B : Finset (Fin m × X))
    (τ : (x : X) → ℕ → Ω x) (hold : FiniteOld f old τ)
    (r : ℕ) (hr : 1 ≤ r) :
    RepairInvariants f old B τ (repairAt f old B τ (r - 1)) r := by sorry

end DynEdgeColorLLL.Main.Supplement
