-- Prove2me | Theorems.Thm_AffDisp4n_case_1
-- name    : AffDisp4n.case_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:04:11.516197+00:00
-- url     : https://prove2.me/theorems/6cee19b7-ccd4-498e-8f82-1bac6e0cb229
-- title:
--   §4.1 Case 1 — a paired parameter has degree $0$ ($\Delta W \le -4$) or at least $2$ ($\Delta W \le 0$), with $\Delta a = 0$
-- statement:
--   Let $\sigma$ be a state valid for the original circuit $C_0$ such that the output check has failed and no deletion (D1)–(D4) or move of an affine gate applies.
--
--   1. If some paired parameter $p$ has $\deg(p) = 0$, there is a state $\sigma'$ valid for $C_0$ with $\Delta m = -1$, $\Delta q = -1$, $\Delta s = 0$ and $\Delta W \le -4$. In the paper, (PF) fixes the partner of $p$ to $0$.
--   2. If some paired parameter $p$ has $\deg(p) \ge 2$, there is a state $\sigma'$ valid for $C_0$ with $\Delta m = -1$, $\Delta q = -1$, $\Delta s = -2$ and $\Delta W \le 0$. In the paper, (PF) fixes $p$ to $0$ and two children of $p$ are deleted by (D1) or (D3).
--
--   In both cases $\Delta a = \Delta m - \Delta q = 0$ and
--   $$
--   \Delta W \le 10\,\Delta a = 0 .
--   $$
--
--   **Formalization Note** `State.Reduced` says that no deletion or move applies, and `¬ OutputSimple` that the output check of §4.1 has failed.
--
--   Differences from the source:
--   - generalization: the current state of the gate elimination algorithm → any state σ valid for C₀ (State.Valid: Φ injective, disjoint pairs, A invertible, at most three nonconstant terms per equation, C(u) = C₀(Φ(u)) on Z(P)); reason: the paper's argument uses only these invariants and every state of the algorithm is valid (§2.4, p.16), so the statement specializes to the algorithm's states
--   - reading: the paragraph describes an operation and its effect (PF fixes r (deg p = 0) or p (deg p ≥ 2) to 0, then two children of p are deleted; ∆m = −1, ∆q = −1, ∆s = 0 or −2, ∆W ≤ −4 or ≤ 0) → there is a state σ′ valid for the same C₀ with these changes of m, q, s and W; reason: the proof of Lemma 4.2 uses exactly the existence of such a successor with these changes; Δa follows from Δm and Δq
--   - encoding: the output check has failed, the deletions and moves of §4.1 no longer apply, and the earlier cases are inapplicable (p.22) → hypotheses ¬ OutputSimple, Reduced and ¬ CaseKApplicable for the earlier cases; reason: the paper's standing assumptions at the point where the case is checked, written out
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §4.1, p.22, "Case 1: a paired parameter has degree zero or at least two"

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

/-- **Case 1: a paired parameter has degree zero or at least two** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §4.1, p.22).
1. If `deg(p) = 0`, (PF) fixes the partner `r` to `0`: "∆m = −1 …, ∆s = 0 …, ∆q = −1 …, and
   ∆a = ∆m − ∆q = 0 … This gives ∆W ≤ −4."
2. If `deg(p) ≥ 2`, (PF) fixes `p` to `0` and two children of `p` are deleted by (D1) or (D3):
   "∆m = −1 …, ∆s = −2 …, ∆q = −1 …, and ∆a = ∆m − ∆q = 0. Thus, we have ∆W ≤ −4 − 2 + 6 = 0."
Each successor is valid for the same original circuit `C₀`.

**Formalization Note** `State.Reduced` says that none of (D1)–(D4) applies and no affine gate can be moved into the
affine system; with `¬ OutputSimple` (the output check of §4.1 failed) these are the conditions under
which the paper checks the cases ("for each case that applies, we may assume that all earlier cases are
inapplicable", p.22). -/
theorem case_1 {n : ℕ} (C₀ : Circuit n) (σ : State n) (hσ : σ.Valid C₀)
    (hout : ¬ σ.OutputSimple) (hred : σ.Reduced) :
    ((∃ p : Fin σ.m, σ.IsPaired p ∧ σ.deg p = 0) →
      ∃ σ' : State n, σ'.Valid C₀ ∧ σ'.m + 1 = σ.m ∧ σ'.q + 1 = σ.q ∧ σ'.s = σ.s ∧
        σ'.W + 4 ≤ σ.W) ∧
    ((∃ p : Fin σ.m, σ.IsPaired p ∧ 2 ≤ σ.deg p) →
      ∃ σ' : State n, σ'.Valid C₀ ∧ σ'.m + 1 = σ.m ∧ σ'.q + 1 = σ.q ∧ σ'.s + 2 = σ.s ∧
        σ'.W ≤ σ.W) := by sorry

end AffDisp4n
