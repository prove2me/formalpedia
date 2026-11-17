-- Prove2me | Theorems.Thm_EulerianLE_Supplement_theorem_40
-- name    : EulerianLE.Supplement.theorem_40
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:19:51.456401+00:00
-- url     : https://prove2.me/theorems/e5ef36ae-1f76-4924-a0f3-62f09da56a77
-- title:
--   Theorem 40 — the OR protocol on an $n$-node oriented ring sends exactly $2n$ pulses
-- statement:
--   Let $v_0,\dots,v_{n-1}$ ($n\ge1$) be an oriented ring with any input bits, where $v_0$ runs Program 9 and every other node Program 10. Then a standalone execution of the OR protocol exists, and every standalone execution sends exactly
--
--   $$2n$$
--
--   pulses in total.
--
--   Each node sends two pulses on every path through its program, so the OR step of the leader-election algorithm costs two pulses per port pair of a circuit.
--
--   **Formalization Note** "Exactly" is an equality: from some time on, the number of pulses sent so far equals $2n$ (`SendsExactly (2 * n)`).
--
--   Differences from the source:
--   - encoding: an oriented ring of n ≥ 1 nodes with designated CW and CCW ports → a network with e : Fin n ≃ V and cw, ccw satisfying IsOrientedRing; reason: same instances
--   - encoding: Programs 9, 10 → the NodeProg automata of orProtocol (CW pulses received at the CCW port); reason: the source's direction convention
--   - reading: the protocol communicates exactly 2n pulses → a fair run exists, and every fair run sends exactly 2n pulses; reason: the count of every execution presupposes that executions exist
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), Theorem 40, p.51 (PDF p.53)

import Mathlib
import Definitions.Def_EulerianLE_Supplement_IsOrientedRing
import Definitions.Def_EulerianLE_Supplement_orProtocol
import Definitions.Def_EulerianLE_Run

namespace EulerianLE.Supplement

/-- **Theorem 40** (Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on
Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), App. D.1, p.51, PDF p.53). The
OR protocol communicates exactly `2n` pulses in total.

On every oriented ring of `n ≥ 1` nodes with any inputs, a standalone execution (fair run) of the OR
protocol (Programs 9 and 10) exists, and every fair run sends exactly `2n` pulses in total.

**Formalization Note.** "Exactly" is an equality (`SendsExactly`: from some time on, the number of
pulses sent so far is `2n`). Existence of a fair run rules out a vacuous "every fair run". -/
theorem theorem_40 (G : Network) (n : ℕ) (e : Fin n ≃ G.V) (cw ccw : ∀ v, Fin (G.deg v))
    (hR : IsOrientedRing G n e cw ccw) (b : Fin n → Bool) :
    (∃ ρ : Run (orProtocol G n hR.1 e cw ccw b) (stdTag _), IsFair ρ) ∧
    ∀ ρ : Run (orProtocol G n hR.1 e cw ccw b) (stdTag _), IsFair ρ → ρ.SendsExactly (2 * n) := by sorry

end EulerianLE.Supplement
