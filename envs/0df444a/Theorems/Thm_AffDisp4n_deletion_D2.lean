-- Prove2me | Theorems.Thm_AffDisp4n_deletion_D2
-- name    : AffDisp4n.deletion_D2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:04:19.935195+00:00
-- url     : https://prove2.me/theorems/9a2eefd6-8526-4963-a3ca-d9a9ceb0de44
-- title:
--   §3.1 (D2) — deleting an unused gate: $\Delta s = -1$, $\Delta W \le -1$
-- statement:
--   Let $\sigma$ be a state valid for the original circuit $C_0$. Suppose that some gate of the acyclic part has no children (no gate reads it) and is not the designated output. Then there is a state $\sigma'$, valid for the same $C_0$, with the same map $\Phi$ and the same pairs, and with
--   $$
--   \Delta m = \Delta q = \Delta a = 0, \qquad \Delta s = -1, \qquad \Delta W \le -1 .
--   $$
--   In the paper, the gate is deleted.
--
--   **Formalization Note** "Valid for $C_0$" (`State.Valid`) collects the invariants of §2.2–§2.6, including $C(u) = C_0(\Phi(u))$ on $Z(P)$, and the new state must be valid for the same original circuit. $\Delta a = 0$ follows from $\Delta m = \Delta q = 0$.
--
--   Differences from the source:
--   - generalization: the current state of the gate elimination algorithm → any state σ valid for C₀ (State.Valid: Φ injective, disjoint pairs, A invertible, at most three nonconstant terms per equation, C(u) = C₀(Φ(u)) on Z(P)); reason: the paper's argument uses only these invariants and every state of the algorithm is valid (§2.4, p.16), so the statement specializes to the algorithm's states
--   - reading: the paragraph describes an operation and its effect (delete the gate; ∆m = ∆q = ∆a = 0, ∆s = −1, ∆W ≤ −1) → there is a state σ′ valid for the same C₀ with the same Φ and the same pairs (State.KeepsMapAndPairs) and these changes of m, q, s and W; reason: the proof of Lemma 4.2 uses exactly the existence of such a successor with these changes; Δa follows from Δm and Δq
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §3.1, p.20, paragraph "D2: deleting an unused gate"

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

/-- **(D2): deleting an unused gate** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §3.1, p.20). "A gate that has no children and is not the designated output can be deleted without changing the computed function. This deletion satisfies ∆m = ∆q = ∆a = 0 …, and ∆s = −1 … Thus, ∆W ≤ −1."
For every state valid for `C₀` in which (D2) applies, there is a state valid for the same `C₀`
with the same map `Φ` and the same pairs ("Each gate deletion removes a gate or an equation without
changing the map Φ", p.19), `Δm = Δq = Δa = 0`, `Δs = −1` and `ΔW ≤ −1`.

**Formalization Note** "Valid for `C₀`" (`State.Valid`) collects the invariants of §2.2–§2.6, including
`C(u) = C₀(Φ(u))` on `Z(P)`; the successor must be valid for the same original circuit. `Δa = 0` follows
from `Δm = Δq = 0`. -/
theorem deletion_D2 {n : ℕ} (C₀ : Circuit n) (σ : State n) (hσ : σ.Valid C₀)
    (happ : σ.D2Applicable) :
    ∃ σ' : State n, σ'.Valid C₀ ∧ σ'.KeepsMapAndPairs σ ∧ σ'.m = σ.m ∧ σ'.q = σ.q ∧ σ'.s + 1 = σ.s ∧
      σ'.W + 1 ≤ σ.W := by sorry

end AffDisp4n
