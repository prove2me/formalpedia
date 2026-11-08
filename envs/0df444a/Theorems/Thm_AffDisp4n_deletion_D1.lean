-- Prove2me | Theorems.Thm_AffDisp4n_deletion_D1
-- name    : AffDisp4n.deletion_D1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:04:05.725221+00:00
-- url     : https://prove2.me/theorems/f7169a5b-0460-4a3a-b104-5010a361977b
-- title:
--   §3.1 (D1) — deleting a gate that depends on at most one input: $\Delta s = -1$, $\Delta W \le -1$
-- statement:
--   Let $\sigma$ be a state valid for the original circuit $C_0$. Suppose that some gate $J$ of the acyclic part either is constant on all parameter assignments in $Z(P)$, or computes a literal $t + c$ of one of its inputs $t$ for every parameter assignment. Then there is a state $\sigma'$, valid for the same $C_0$, with the same map $\Phi$ and the same pairs, and with
--   $$
--   \Delta m = \Delta q = \Delta a = 0, \qquad \Delta s = -1, \qquad \Delta W \le -1 .
--   $$
--   In the paper, $J$ is rerouted to the constant or literal and deleted.
--
--   **Formalization Note** "Valid for $C_0$" (`State.Valid`) collects the invariants of §2.2–§2.6, including $C(u) = C_0(\Phi(u))$ on $Z(P)$, and the new state must be valid for the same original circuit. $\Delta a = 0$ follows from $\Delta m = \Delta q = 0$.
--
--   Differences from the source:
--   - generalization: the current state of the gate elimination algorithm → any state σ valid for C₀ (State.Valid: Φ injective, disjoint pairs, A invertible, at most three nonconstant terms per equation, C(u) = C₀(Φ(u)) on Z(P)); reason: the paper's argument uses only these invariants and every state of the algorithm is valid (§2.4, p.16), so the statement specializes to the algorithm's states
--   - reading: the paragraph describes an operation and its effect (reroute J to the constant or literal of its input and delete J; ∆m = ∆q = ∆a = 0, ∆s = −1, ∆W ≤ −1) → there is a state σ′ valid for the same C₀ with the same Φ and the same pairs (State.KeepsMapAndPairs) and these changes of m, q, s and W; reason: the proof of Lemma 4.2 uses exactly the existence of such a successor with these changes; Δa follows from Δm and Δq
--   - reading: a gate J computes a constant or a literal of one of its inputs; in addition, a gate that becomes constant on all parameter assignments in Z(P) → ∃ c, ∀ u ∈ Z(P), J(u) = c, or ∃ c, ∀ u, J(u) = (first or second input of J)(u) + c; reason: the paper's examples of literals (unary gates, constant or identical inputs, AND with dependent linear parts) are identities in u; constants are taken on Z(P) as the paper's last sentence says
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §3.1, pp.19–20, paragraph "D1: deleting a gate that depends on at most one input"

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

/-- **(D1): deleting a gate that depends on at most one input** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §3.1, pp.19–20). If a gate of the acyclic part computes a constant on `Z(P)`, or a literal of one of its inputs, it is rerouted to that constant or literal and deleted: "we have ∆m = ∆q = ∆a = 0 (as no parameters or pairs are changed), and ∆s = −1 (as one gate is deleted). Thus, ∆W ≤ −1."
For every state valid for `C₀` in which (D1) applies, there is a state valid for the same `C₀`
with the same map `Φ` and the same pairs ("Each gate deletion removes a gate or an equation without
changing the map Φ", p.19), `Δm = Δq = Δa = 0`, `Δs = −1` and `ΔW ≤ −1`.

**Formalization Note** "Valid for `C₀`" (`State.Valid`) collects the invariants of §2.2–§2.6, including
`C(u) = C₀(Φ(u))` on `Z(P)`; the successor must be valid for the same original circuit. `Δa = 0` follows
from `Δm = Δq = 0`. -/
theorem deletion_D1 {n : ℕ} (C₀ : Circuit n) (σ : State n) (hσ : σ.Valid C₀)
    (happ : σ.D1Applicable) :
    ∃ σ' : State n, σ'.Valid C₀ ∧ σ'.KeepsMapAndPairs σ ∧ σ'.m = σ.m ∧ σ'.q = σ.q ∧ σ'.s + 1 = σ.s ∧
      σ'.W + 1 ≤ σ.W := by sorry

end AffDisp4n
