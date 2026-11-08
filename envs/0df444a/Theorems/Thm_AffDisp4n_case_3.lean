-- Prove2me | Theorems.Thm_AffDisp4n_case_3
-- name    : AffDisp4n.case_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:04:10.13486+00:00
-- url     : https://prove2.me/theorems/6960910f-4f8a-4212-accf-4f03e1cbe35b
-- title:
--   §4.1 Case 3 — a paired parameter occurs in the affine system: $\Delta a = 0$, $\Delta W \le 0$
-- statement:
--   Let $\sigma$ be a state valid for the original circuit $C_0$ such that the output check has failed, no deletion (D1)–(D4) or move of an affine gate applies, and neither Case 1 nor Case 2 applies. Suppose that some paired parameter occurs in the affine system. Then there is a state $\sigma'$ valid for $C_0$ with
--   $$
--   \Delta m = -1, \quad \Delta q = -1, \quad \Delta s = -2, \quad \Delta a = 0, \quad \Delta W \le 0 .
--   $$
--   In the paper, (PF) fixes the partner $r$ to $0$, the unique child $H_r$ of $r$ is deleted, and then the unique child $H_p$ of $p$ is deleted by (D3) or (D4).
--
--   **Formalization Note** `State.Reduced` says that no deletion or move applies, and `¬ OutputSimple` that the output check of §4.1 has failed.
--
--   Differences from the source:
--   - generalization: the current state of the gate elimination algorithm → any state σ valid for C₀ (State.Valid: Φ injective, disjoint pairs, A invertible, at most three nonconstant terms per equation, C(u) = C₀(Φ(u)) on Z(P)); reason: the paper's argument uses only these invariants and every state of the algorithm is valid (§2.4, p.16), so the statement specializes to the algorithm's states
--   - reading: the paragraph describes an operation and its effect (PF fixes r to 0, H_r and H_p are deleted; ∆m = −1, ∆s = −2, ∆q = −1, ∆W ≤ 0) → there is a state σ′ valid for the same C₀ with these changes of m, q, s and W; reason: the proof of Lemma 4.2 uses exactly the existence of such a successor with these changes; Δa follows from Δm and Δq
--   - encoding: the output check has failed, the deletions and moves of §4.1 no longer apply, and the earlier cases are inapplicable (p.22) → hypotheses ¬ OutputSimple, Reduced and ¬ CaseKApplicable for the earlier cases; reason: the paper's standing assumptions at the point where the case is checked, written out
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §4.1, p.23, "Case 3: a paired parameter occurs in the affine system"

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Acyclic_gateVal
import Definitions.Def_AffDisp4n_Acyclic_eval
import Definitions.Def_AffDisp4n_Circuit
import Definitions.Def_AffDisp4n_Acyclic_mapInput
import Definitions.Def_AffDisp4n_Acyclic_Reads
import Definitions.Def_AffDisp4n_PairsDisjoint
import Definitions.Def_AffDisp4n_Z
import Definitions.Def_AffDisp4n_IsAffineOp
import Definitions.Def_AffDisp4n_IsAndOp
import Definitions.Def_AffDisp4n_State
import Definitions.Def_AffDisp4n_State_Phi
import Definitions.Def_AffDisp4n_State_eval
import Definitions.Def_AffDisp4n_State_Valid
import Definitions.Def_AffDisp4n_State_s
import Definitions.Def_AffDisp4n_State_q
import Definitions.Def_AffDisp4n_State_a
import Definitions.Def_AffDisp4n_State_IsPaired
import Definitions.Def_AffDisp4n_State_deg
import Definitions.Def_AffDisp4n_State_W
import Definitions.Def_AffDisp4n_State_D1Applicable
import Definitions.Def_AffDisp4n_State_D2Applicable
import Definitions.Def_AffDisp4n_State_D3Applicable
import Definitions.Def_AffDisp4n_State_D4Applicable
import Definitions.Def_AffDisp4n_State_AffineMovable
import Definitions.Def_AffDisp4n_State_Reduced
import Definitions.Def_AffDisp4n_State_OutputSimple
import Definitions.Def_AffDisp4n_State_Case1Applicable
import Definitions.Def_AffDisp4n_State_Case2Applicable
import Definitions.Def_AffDisp4n_State_Case3Applicable

namespace AffDisp4n

/-- **Case 3: a paired parameter occurs in the affine system** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §4.1, p.23). If Cases 1 and 2 do
not apply and a paired parameter `p` (partner `r`) occurs in an equation, (PF) fixes `r` to `0`, the
unique child `H_r` of `r` is deleted, and then the unique child `H_p` of `p` is deleted by (D3) or (D4):
"∆m = −1 …, ∆s = −2 (as H_r and H_p are deleted), ∆q = −1 …, and ∆a = ∆m − ∆q = 0. This gives,
∆W ≤ −4 − 2 + 6 = 0." The successor is valid for the same original circuit `C₀`.

**Formalization Note** `State.Reduced` says that none of (D1)–(D4) applies and no affine gate can be moved into the
affine system; with `¬ OutputSimple` (the output check of §4.1 failed) these are the conditions under
which the paper checks the cases ("for each case that applies, we may assume that all earlier cases are
inapplicable", p.22). -/
theorem case_3 {n : ℕ} (C₀ : Circuit n) (σ : State n) (hσ : σ.Valid C₀)
    (hout : ¬ σ.OutputSimple) (hred : σ.Reduced)
    (h1 : ¬ σ.Case1Applicable) (h2 : ¬ σ.Case2Applicable) (h3 : σ.Case3Applicable) :
    ∃ σ' : State n, σ'.Valid C₀ ∧ σ'.m + 1 = σ.m ∧ σ'.q + 1 = σ.q ∧ σ'.s + 2 = σ.s ∧
      σ'.W ≤ σ.W := by sorry

end AffDisp4n
