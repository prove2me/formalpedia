-- Prove2me | Theorems.Thm_EntanglementParadigm_eq_2_converse
-- name    : EntanglementParadigm.eq_2_converse
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:27:51.431845+00:00
-- url     : https://prove2.me/theorems/61b295a0-1785-4830-bed3-ed1db2c1d4cb
-- title:
--   Eq. (2), converse half: every achievable rate is at least $\tfrac12 I(A:B|C)$
-- statement:
--   Let $\psi$ be a pure state on the finite registers $B\otimes A'\otimes A\otimes C$, and let $\rho_{ABC}=\operatorname{Tr}_{A'}\psi$. Alice holds $A$ and $A'$, Charlie holds $C$, and Bob's $B$ is passive. If $Q$ is an achievable rate for redistributing $A$ from Alice to Charlie, with arbitrary free shared assistance, then
--
--   $$
--   Q\ \ge\ \tfrac12\, I(A:B|C)_\rho ,
--   $$
--
--   where $I(A:B|C)=S(AC)+S(BC)-S(ABC)-S(C)$ in bits.
--
--   This is the lower half of the optimal rate $Q_{A'C}=\tfrac12 I(A:B|C)$ of state redistribution, and it gives the inequality $\ge E_{sq}$ in Theorem 1.
--
--   Differences from the source:
--   - reading: "the rate of quantum communication that is required", never defined formally → IsAchievableRate: for all ε, δ > 0 and all large n, a protocol on ψ^{⊗n} with fidelity ≥ 1 − ε and log₂ dim Q ≤ n(Q + δ); reason: the standard block-coding meaning, that of the paper's reference [10]; the rate is operational, never the formula ½I(A:B|C)
--   - reading: "arbitrary shared entanglement" → any finite shared density matrix independent of the state, of any size and at no charge (Redistribution.assistance); reason: the widest reading: the lower bound covers every such protocol, and Bell pairs are a special case
--   - reading: "local operations and the sending of qubits" → one CPTP encoder at the sender, one forward message, one CPTP decoder at the receiver, no classical communication; reason: p.2 excludes classical communication and the paper's reference [10] is one-way
--   - reading: no statement on dimension → every register finite, with no bound on any dimension; reason: qubit counting, the entropies of Eq. (2) and the paper's references [4], [10] are finite-dimensional
--   - encoding: fidelity of the total pure state, convention unstated → squared fidelity (Information100.P53.fidelity); reason: the requirement is fidelity → 1, on which both conventions agree
--   - encoding: registers B, A′, A, C → ordered B × (R × (A × C)) with R the paper's A′; positive dimensions Fin (k + 1); reason: Lean convention, the order of Intakenext100.P75; same instances
--   - encoding: qubit rates and entropies with no stated base → logb 2 of the message dimension, von Neumann entropy in bits; reason: Eq. (2) equates a qubit rate with ½I, which fixes base 2
--   - encoding: Eq. (2) as one equality Q_A′C = ½ I(A : B|C) → the lower bound only, named as the converse half; reason: the other half is the platform's open item Intakenext100.P75.redistribution_achievability, which is not posed again; the goal holds the whole value
-- source:
--   J. Oppenheim, A paradigm for entanglement theory based on quantum communication, arXiv:0801.0458v1, Eq. (2), p.2

import Definitions.Def_EntanglementParadigm_IsAchievableRate

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)
open QAlgorithms.Papers.Independent.Intakenext100.P75 (conditionedLastCMIBits discardReference)

namespace EntanglementParadigm

/-- Oppenheim, arXiv:0801.0458v1, Eq. (2), p.2, converse half: for a pure state `ψ` on
`B A′ A C`, every achievable rate is at least `½ I(A : B|C)`, against arbitrary assistance.

**Formalization Note.** Registers are ordered `B × (R × (A × C))`, with `R` the paper's `A′`.
`conditionedLastCMIBits (discardReference ψ)` is `I(A : B|C)` in bits. Rates are in qubits.
Nonemptiness of the registers follows from `IsPure`. The achievability half of Eq. (2) is
`Intakenext100.P75.redistribution_achievability`. -/
theorem eq_2_converse {A B C R : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
    (ψ : Mat (B × (R × (A × C)))) (hψ : IsPure ψ) (Q : ℝ) (hQ : IsAchievableRate ψ Q) :
    conditionedLastCMIBits (discardReference ψ) / 2 ≤ Q := by sorry

end EntanglementParadigm
