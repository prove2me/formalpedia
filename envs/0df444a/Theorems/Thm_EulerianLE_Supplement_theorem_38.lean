-- Prove2me | Theorems.Thm_EulerianLE_Supplement_theorem_38
-- name    : EulerianLE.Supplement.theorem_38
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:19:23.383569+00:00
-- url     : https://prove2.me/theorems/0a8ed7a1-c1f7-4de0-abd7-3ac2e7458d8e
-- title:
--   Theorem 38 — the OR protocol on an oriented ring terminates quiescently with $v_0$ last, outputs the OR, and names the witness of Definition 6
-- statement:
--   Let $v_0,\dots,v_{n-1}$ ($n\ge1$) be an oriented ring in clockwise order, node $v_i$ with input bit $b_i$, where the OR initiator $v_0$ runs Program 9 and every other node Program 10. Then:
--
--   1. **Termination.** A standalone execution exists, and in every standalone execution the protocol is quiescently terminating (every pulse sent to a node is consumed before that node terminates) and every node other than $v_0$ terminates strictly before $v_0$.
--   2. **Output.** Every node outputs $\bigvee_{i} b_i$.
--   3. **Witness.** If $\bigvee_i b_i=1$, let $j=\min\{i\in\{0,\dots,n-1\}: b_i=1\}$ (Definition 6, $v_0$ included). Then $v_j$ outputs $(1,\text{witness})$ and every other node outputs $(1,\text{non-witness})$.
--
--   The OR protocol is the black box that the leader-election algorithm runs on each circuit to decide whether a node that is still counting exists, and to find the relay node that merges circuits.
--
--   **Formalization Note** Items 2 and 3 are stated together: if all inputs are 0, every node completes with output `.zero`; otherwise $v_j$ completes with `.one true` and every other node with `.one false`. Quiescence is the published `Run.Quiescent`; "$v_0$ last" compares completion steps.
--
--   Differences from the source:
--   - encoding: an oriented ring of n ≥ 1 nodes v0, …, v_{n−1} in CW order with designated CW and CCW ports → a network with a bijection e : Fin n ≃ V and port choices cw, ccw satisfying IsOrientedRing (degree 2, cw ≠ ccw, link of v_i's CW port = v_{i+1}'s CCW port); reason: same instances, n = 1 and n = 2 included as in the source
--   - encoding: Send / BlockingRecv / "the pulse is CW" in Programs 9, 10 → NodeProg automata in which a CW pulse is tested and consumed at the receiver's CCW port, and "wait until a pulse arrives" tests the CCW port first; reason: the source's direction convention (a CCW pulse completing a traversal returns at the CW port); both ports never hold a pulse when the protocol waits
--   - reading: the protocol is quiescently terminating → a fair run exists, and every fair run is quiescent with every node completing; reason: termination of every execution presupposes that executions exist
--   - reading: v0 the last to terminate → every other node completes at a step strictly before v0's completion step; reason: "last" of a terminating set of nodes
--   - encoding: outputs 0, (1, witness), (1, non-witness) → OrOut .zero, .one true, .one false, with (ii) and (iii) stated as one case split on whether some input is 1; reason: same content
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), Theorem 38, pp.48–49 (PDF pp.50–51); Definition 6, p.48 (PDF p.50); Programs 9, 10, pp.49–50 (PDF pp.51–52)

import Mathlib
import Definitions.Def_EulerianLE_Supplement_IsOrientedRing
import Definitions.Def_EulerianLE_Supplement_orProtocol
import Definitions.Def_EulerianLE_Run

namespace EulerianLE.Supplement

/-- **Theorem 38** (Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on
Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), App. D.1, pp.48–49, PDF
pp.50–51). The OR protocol in Programs 9 and 10 satisfies the following. (i) Termination. The protocol
is quiescently terminating with v₀ the last to terminate. (ii) Output. Every node outputs the bit-wise
OR of all inputs. (iii) Witness. If the OR is 1, exactly one node outputs it is the witness; this node
is the witness of Definition 6. All other nodes output they are not the witness.

On every oriented ring `vᵢ = e i` (`n ≥ 1`) with inputs `b : Fin n → Bool`:

* a standalone execution (fair run) of the OR protocol exists;
* in every fair run the execution is quiescent, and every node other than `v₀` completes at a step
  strictly before every completion step of `v₀`;
* if every input is `0`, every node completes with output `0`;
* otherwise, with `j` the least index with `b j = 1` (Definition 6, `v₀` included), `v_j` completes
  with output `(1, witness)` and every other node with `(1, non-witness)`.

**Formalization Note.** Existence of a fair run rules out a vacuous "every fair run". Outputs: `.zero`
is 0, `.one true` is (1, witness), `.one false` is (1, non-witness). -/
theorem theorem_38 (G : Network) (n : ℕ) (e : Fin n ≃ G.V) (cw ccw : ∀ v, Fin (G.deg v))
    (hR : IsOrientedRing G n e cw ccw) (b : Fin n → Bool) :
    (∃ ρ : Run (orProtocol G n hR.1 e cw ccw b) (stdTag _), IsFair ρ) ∧
    ∀ ρ : Run (orProtocol G n hR.1 e cw ccw b) (stdTag _), IsFair ρ →
      ρ.Quiescent ∧
      (∀ w, w ≠ e ⟨0, hR.1⟩ → ∃ tw, ρ.CompletesAt w tw ∧
        ∀ t₀, ρ.CompletesAt (e ⟨0, hR.1⟩) t₀ → tw < t₀) ∧
      ((∀ i, b i = false) → ∀ i, ρ.CompletesWith (e i) .zero) ∧
      ((∃ i, b i = true) → ∃ j, b j = true ∧ (∀ i, i < j → b i = false) ∧
        ∀ i, ρ.CompletesWith (e i) (.one (decide (i = j)))) := by sorry

end EulerianLE.Supplement
