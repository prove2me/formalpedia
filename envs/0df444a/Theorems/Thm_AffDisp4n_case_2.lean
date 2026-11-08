-- Prove2me | Theorems.Thm_AffDisp4n_case_2
-- name    : AffDisp4n.case_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:04:09.420765+00:00
-- url     : https://prove2.me/theorems/4574fd32-1acd-4ff7-8db9-de38964dea68
-- title:
--   §4.1 Case 2 — two partners have the same child: $\Delta a = 0$, $\Delta W \le -5$
-- statement:
--   Let $\sigma$ be a state valid for the original circuit $C_0$ such that the output check has failed, no deletion (D1)–(D4) or move of an affine gate applies, and Case 1 does not apply. Suppose that some pair $\{p, r\} \in P$ has a common child $H$. Then there is a state $\sigma'$ valid for $C_0$ with
--   $$
--   \Delta m = -1, \quad \Delta q = -1, \quad \Delta s = -1, \quad \Delta a = 0, \quad \Delta W \le -5 .
--   $$
--   In the paper, (PF) restricts the pair to a line of $pr = 0$ on which $H$ is constant (a gate), or imposes $p = r + 1$ (an equation $v + p + r = c$), and $H$ is deleted.
--
--   **Formalization Note** `State.Reduced` says that no deletion or move applies, and `¬ OutputSimple` that the output check of §4.1 has failed.
--
--   Differences from the source:
--   - generalization: the current state of the gate elimination algorithm → any state σ valid for C₀ (State.Valid: Φ injective, disjoint pairs, A invertible, at most three nonconstant terms per equation, C(u) = C₀(Φ(u)) on Z(P)); reason: the paper's argument uses only these invariants and every state of the algorithm is valid (§2.4, p.16), so the statement specializes to the algorithm's states
--   - reading: the paragraph describes an operation and its effect (PF restricts the pair so that H becomes constant, H is deleted; ∆m = −1, ∆s = −1, ∆q = −1, ∆W ≤ −5) → there is a state σ′ valid for the same C₀ with these changes of m, q, s and W; reason: the proof of Lemma 4.2 uses exactly the existence of such a successor with these changes; Δa follows from Δm and Δq
--   - encoding: the output check has failed, the deletions and moves of §4.1 no longer apply, and the earlier cases are inapplicable (p.22) → hypotheses ¬ OutputSimple, Reduced and ¬ CaseKApplicable for the earlier cases; reason: the paper's standing assumptions at the point where the case is checked, written out
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §4.1, pp.22–23, "Case 2: two partners have the same child"

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

/-- **Case 2: two partners have the same child** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §4.1, pp.22–23). If Case 1 does not apply and a
pair `{p, r} ∈ P` has a common child `H`, one member of the pair is restricted by (PF) so that `H`
becomes constant (a gate) or reduces to `v = c + 1` (an equation), and `H` is deleted: "∆m = −1 …,
∆s = −1 (as H is deleted), ∆q = −1 …, and ∆a = ∆m − ∆q = 0. This gives ∆W ≤ −4 − 1 = −5." The successor
is valid for the same original circuit `C₀`.

**Formalization Note** `State.Reduced` says that none of (D1)–(D4) applies and no affine gate can be moved into the
affine system; with `¬ OutputSimple` (the output check of §4.1 failed) these are the conditions under
which the paper checks the cases ("for each case that applies, we may assume that all earlier cases are
inapplicable", p.22). -/
theorem case_2 {n : ℕ} (C₀ : Circuit n) (σ : State n) (hσ : σ.Valid C₀)
    (hout : ¬ σ.OutputSimple) (hred : σ.Reduced)
    (h1 : ¬ σ.Case1Applicable) (h2 : σ.Case2Applicable) :
    ∃ σ' : State n, σ'.Valid C₀ ∧ σ'.m + 1 = σ.m ∧ σ'.q + 1 = σ.q ∧ σ'.s + 1 = σ.s ∧
      σ'.W + 5 ≤ σ.W := by sorry

end AffDisp4n
