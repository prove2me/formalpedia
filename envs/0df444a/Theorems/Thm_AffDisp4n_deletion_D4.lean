-- Prove2me | Theorems.Thm_AffDisp4n_deletion_D4
-- name    : AffDisp4n.deletion_D4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:04:27.939766+00:00
-- url     : https://prove2.me/theorems/d78cb9ab-d562-45ff-94e0-f2a697bcc467
-- title:
--   §3.1 (D4) — unit parameter deletion: $\Delta s = -1$, $\Delta W \le -1$
-- statement:
--   Let $\sigma$ be a state valid for the original circuit $C_0$. Suppose that some unpaired parameter $x$ is isolated (degree $1$) and its unique child is an equation $E$. Then there is a state $\sigma'$, valid for the same $C_0$, with the same pairs and the same image of $\Phi$, and with
--   $$
--   \Delta m = \Delta q = \Delta a = 0, \qquad \Delta s = -1, \qquad \Delta W \le -1 .
--   $$
--   In the paper, $x$ is exchanged by (AR) with an auxiliary variable $Q$ that depends on it, and then $x$, now an auxiliary variable, is deleted together with $E$.
--
--   **Formalization Note** "Valid for $C_0$" (`State.Valid`) collects the invariants of §2.2–§2.6, including $C(u) = C_0(\Phi(u))$ on $Z(P)$, and the new state must be valid for the same original circuit. $\Delta a = 0$ follows from $\Delta m = \Delta q = 0$.
--
--   Differences from the source:
--   - generalization: the current state of the gate elimination algorithm → any state σ valid for C₀ (State.Valid: Φ injective, disjoint pairs, A invertible, at most three nonconstant terms per equation, C(u) = C₀(Φ(u)) on Z(P)); reason: the paper's argument uses only these invariants and every state of the algorithm is valid (§2.4, p.16), so the statement specializes to the algorithm's states
--   - reading: the paragraph describes an operation and its effect (exchange x with an auxiliary variable Q by (AR), then delete x and E; ∆m = ∆q = ∆a = 0, ∆s = −1, ∆W ≤ −1) → there is a state σ′ valid for the same C₀ with the same pairs (State.KeepsPairs), the same image of Φ and these changes of m, q, s and W; reason: the proof of Lemma 4.2 uses exactly the existence of such a successor with these changes; Δa follows from Δm and Δq
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §3.1, p.20, paragraph "D4: unit parameter deletion"

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
import Definitions.Def_AffDisp4n_State_KeepsMapAndPairs
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

/-- **(D4): unit parameter deletion** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §3.1, p.20). "Consider an unpaired, isolated parameter x whose unique child is an equation E. We exchange x with a suitable auxiliary variable Q using the (AR) operation, and then delete x, which is now an auxiliary variable, together with equation E." Then "∆m = ∆q = ∆a = 0. Moreover, ∆s = −1 because equation E is deleted, so ∆W ≤ −1."
For every state valid for `C₀` in which (D4) applies, there is a state valid for the same `C₀`
with the same pairs, the same image of `Φ` (the map changes only by (AR), which keeps `im Φ`, §2.4, p.16),
`Δm = Δq = Δa = 0`, `Δs = −1` and `ΔW ≤ −1`.

**Formalization Note** "Valid for `C₀`" (`State.Valid`) collects the invariants of §2.2–§2.6, including
`C(u) = C₀(Φ(u))` on `Z(P)`; the successor must be valid for the same original circuit. `Δa = 0` follows
from `Δm = Δq = 0`. -/
theorem deletion_D4 {n : ℕ} (C₀ : Circuit n) (σ : State n) (hσ : σ.Valid C₀)
    (happ : σ.D4Applicable) :
    ∃ σ' : State n, σ'.Valid C₀ ∧ σ'.KeepsPairs σ ∧ Set.range σ'.Phi = Set.range σ.Phi ∧ σ'.m = σ.m ∧
      σ'.q = σ.q ∧ σ'.s + 1 = σ.s ∧ σ'.W + 1 ≤ σ.W := by sorry

end AffDisp4n
