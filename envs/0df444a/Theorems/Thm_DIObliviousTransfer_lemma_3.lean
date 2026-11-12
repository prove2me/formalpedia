-- Prove2me | Theorems.Thm_DIObliviousTransfer_lemma_3
-- name    : DIObliviousTransfer.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T09:04:29.812028+00:00
-- url     : https://prove2.me/theorems/50403512-e543-409a-a873-9963a3d3b1b3
-- title:
--   Lemma 3 — eliminating bounded interactive communication
-- statement:
--   Let $S$ be a two-laboratory window strategy from an arbitrary initial state, reference included, that exchanges at most $c$ classical bits and $q$ qubits on every branch. The classical budget includes adaptive control symbols; scheduled control symbols are free.
--
--   Then there is a strategy $S_0$ with no communication in the window. It acts on the original registers together with additional registers prepared in a fixed resource state and holding two flags. On the branch where both flags are set, its state on the original registers, reference included, equals $2^{-(c+2q)}$ times the final state of $S$. Consequently, for every event $E$ on the original registers and $b=c+q$,
--   $$\Pr_{S_0}(E)\ge2^{-(c+2q)}\Pr_S(E)\ge2^{-2b}\Pr_S(E).$$
--
--   Differences from the source:
--
--   - reading: adaptive bidirectional messages of total cost at most ℓ qubits, every adaptive control symbol charged in a self-delimiting transcript, fixed public schedule free → window steps emitting a control symbol (classical length, quantum length, next active side), scheduled or adaptive; cost = classical bits + Elias-γ encodings of adaptive control symbols + qubits; a message exceeding the remaining budget closes the window undelivered; reason: Decision D5 (Definition 3 (i)-(ii)); enforcing the budget is equivalent to quantifying over admissible strategies since both sides see the control transcript
--   - encoding: quantum systems and strategies in the abstract (registers, measurements, instruments) → finite-dimensional registers, matrices over finite types, POVMs and Kraus instruments; reason: Decision D2: registers are polynomial-size or finite-alphabet throughout; same instances
--   - encoding: every event E; S₀ respects the prescribed causal order → events are operators 0 ≤ E ≤ 1 on the original registers; S₀ is a window strategy whose control symbols are all scheduled with zero lengths; reason: an event of the final state is such an operator; a scheduled order is a fixed causal order
--   - generalization: for every event E there exists S₀ → one S₀ (and one resource state ω) works for every event E at once; reason: the page's last sentence (the state of S₀ on the original registers on the correct-guess branch is that of S) makes S₀ independent of E; the Lean specializes to the page's ∀E ∃S₀
--   - reading: S₀ has no communication in the window, with arbitrary prior entanglement permitted → S₀ acts on the original registers plus fresh registers in a fixed pre-window resource state ω (shared entanglement and randomness), each laboratory holding one guess flag; reason: prior entanglement is permitted by the window model (Definition 3, Lemma 3 "with arbitrary prior entanglement"), and the transcript-guessing and teleportation proof uses exactly such a pre-shared resource
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Lemma 3, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_DIObliviousTransfer_WinStrat

namespace DIObliviousTransfer

open Matrix
open scoped ComplexOrder

/-- **Lemma 3 (Eliminating bounded interactive communication)**, Batra, Chen, Jain, Zhang,
arXiv:2610.01421 (held version, sha256 8334c039…), p.15 (PDF p.17). Let a window strategy `S`
exchange at most `c` classical bits (adaptive control included, scheduled control free) and `q`
qubits on every branch, from an arbitrary initial state of the two laboratories and a reference.
Then there is a strategy `S₀` without communication in that window, on the original registers
together with additional registers prepared in a fixed resource state (shared entanglement and
randomness) and holding two flags, such that on the branch where both flags are set its state on
the original registers, reference included, is `2^{−(c+2q)}` times the final state of `S`;
consequently for every event `E` (an operator `0 ≤ E ≤ 1` on the original registers)
`Pr_{S₀}(E) ≥ 2^{−(c+2q)} Pr_S(E) ≥ 2^{−2b} Pr_S(E)`, `b = c + q`.

**Formalization Note** (decision D5). Windows, costs and the move of port qubits are those of
`WinStrat`; "every branch" is every branch of nonzero weight. `S₀` is a window strategy of the
same kind whose control symbols are all scheduled with zero lengths (`NoComm`), so it exchanges
nothing and keeps a fixed order of local activations. -/
theorem lemma_3 {P : ℕ} {HA HB HR : Type} [Fintype HA] [Fintype HB] [Fintype HR] [DecidableEq HA]
    [DecidableEq HB] [DecidableEq HR] (S : WinStrat P HA HB)
    (ρ : Matrix ((LabReg P HA × LabReg P HB) × HR) ((LabReg P HA × LabReg P HB) × HR) ℂ)
    (hρ : IsState ρ) (c q : ℕ)
    (hcost : ∀ br ∈ S.branches ρ, br.2.trace ≠ 0 → S.classCost br.1 ≤ c ∧
      WinStrat.quantCost br.1 ≤ q) :
    ∃ (YA YB : Type) (_ : Fintype YA) (_ : Fintype YB) (_ : DecidableEq YA) (_ : DecidableEq YB)
      (ω : Matrix ((Bool × YA) × (Bool × YB)) ((Bool × YA) × (Bool × YB)) ℂ)
      (S₀ : WinStrat P (HA × (Bool × YA)) (HB × (Bool × YB))),
      IsState ω ∧ S₀.NoComm ∧
      flaggedPart (S₀.final (withResource ρ ω)) = ((2 : ℂ) ^ (c + 2 * q))⁻¹ • S.final ρ ∧
      ∀ E : Matrix ((LabReg P HA × LabReg P HB) × HR) ((LabReg P HA × LabReg P HB) × HR) ℂ,
        E.PosSemidef → (1 - E).PosSemidef →
        ((2 : ℝ) ^ (c + 2 * q))⁻¹ * (E * S.final ρ).trace.re ≤
            (E * traceResource (S₀.final (withResource ρ ω))).trace.re ∧
          ((2 : ℝ) ^ (2 * (c + q)))⁻¹ * (E * S.final ρ).trace.re ≤
            ((2 : ℝ) ^ (c + 2 * q))⁻¹ * (E * S.final ρ).trace.re := by sorry

end DIObliviousTransfer
