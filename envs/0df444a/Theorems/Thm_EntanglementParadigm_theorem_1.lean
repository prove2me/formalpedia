-- Prove2me | Theorems.Thm_EntanglementParadigm_theorem_1
-- name    : EntanglementParadigm.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:29:33.216598+00:00
-- url     : https://prove2.me/theorems/1ccbcff3-b8ad-4555-a432-377e4ce6aa34
-- title:
--   Theorem 1: the optimal redistribution rate over arbitrary side-information is $E_{sq}(A:B)$
-- statement:
--   Let $\rho_{AB}$ be a density matrix on finite registers. Alice holds $A$ and wants to send it to Charlie while Bob, holding $B$, stays passive. A distributor gives side-information: a pure state $\psi$ on $B\otimes A'\otimes A\otimes C$ with $AB$ marginal $\rho_{AB}$, where $A'$ goes to Alice and $C$ to Charlie. With a noiseless quantum channel and arbitrary free shared entanglement, let $Q_{A'C}$ be the infimum of the achievable rates for $\psi$. Then
--
--   $$
--   \inf_{\rho_{A'C}} Q_{A'C}=E_{sq}(A:B),
--   $$
--
--   where $E_{sq}$ is the squashed entanglement. Equivalently, $E_{sq}(A:B)$ is the greatest lower bound of the set of all rates achievable with some side-information: no rate below it is achievable, whatever the side-information, and rates arbitrarily close to it are achievable.
--
--   The theorem gives the squashed entanglement an operational meaning: it is the fastest rate at which one share of a state can be sent when sender and receiver are given the best possible side-information.
--
--   Differences from the source:
--   - encoding: inf_{ρ_A′C} inf Q_A′C = E_sq(A : B) → IsGLB of the union, over all side-information, of the achievable rates; reason: IsGLB on the union is the iterated infimum and holds no sInf junk
--   - encoding: E_sq as inf_Λ ½ I(A : B|Λ(E)), Eq. (1) → Dependency50.P19.squashed, the infimum of ½I over all finite extensions of ρ; reason: the two agree by Gap48.P32.fixed_purification_channels, a milestone of this mission
--   - reading: "the rate of quantum communication that is required", never defined formally → IsAchievableRate: for all ε, δ > 0 and all large n, a protocol on ψ^{⊗n} with fidelity ≥ 1 − ε and log₂ dim Q ≤ n(Q + δ); reason: the standard block-coding meaning, that of the paper's reference [10]; the rate is operational, never the formula ½I(A:B|C)
--   - reading: "arbitrary shared entanglement" → any finite shared density matrix independent of the state, of any size and at no charge (Redistribution.assistance); reason: the widest reading: the lower bound covers every such protocol, and Bell pairs are a special case
--   - reading: "local operations and the sending of qubits" → one CPTP encoder at the sender, one forward message, one CPTP decoder at the receiver, no classical communication; reason: p.2 excludes classical communication and the paper's reference [10] is one-way
--   - reading: "inf … taken over states ρ_A′C", copies not discussed for the side-information → one single-copy state ψ, used as ψ^{⊗n}; reason: Eq. (4) and Eq. (1) are single-copy, and block side-information appears only for Theorem 3, Eq. (11)
--   - reading: no statement on dimension → every register finite, with no bound on any dimension; reason: qubit counting, the entropies of Eq. (2) and the paper's references [4], [10] are finite-dimensional
--   - encoding: fidelity of the total pure state, convention unstated → squared fidelity (Information100.P53.fidelity); reason: the requirement is fidelity → 1, on which both conventions agree
--   - encoding: registers B, A′, A, C → ordered B × (R × (A × C)) with R the paper's A′; positive dimensions Fin (k + 1); reason: Lean convention, the order of Intakenext100.P75; same instances
--   - encoding: qubit rates and entropies with no stated base → logb 2 of the message dimension, von Neumann entropy in bits; reason: Eq. (2) equates a qubit rate with ½I, which fixes base 2
-- source:
--   J. Oppenheim, A paradigm for entanglement theory based on quantum communication, arXiv:0801.0458v1, Theorem 1, p.2

import Definitions.Def_EntanglementParadigm_IsSideInformation
import Definitions.Def_EntanglementParadigm_IsAchievableRate
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Dependency50.P19 (squashed)

namespace EntanglementParadigm

/-- Oppenheim, arXiv:0801.0458v1, Theorem 1, p.2: given a state `ρ_AB` and arbitrary
side-information `ρ_A′C`, `inf Q_A′C = E_sq(A : B)`, the infimum taken over states `ρ_A′C`.

**Formalization Note.** `IsGLB` on the union of the achievable rates over all side-information is
the form of `inf_{ρ_A′C} inf_{Q achievable} Q`: every achievable rate with every side-information
is at least `E_sq`, and rates arbitrarily close to `E_sq` are achievable. It holds no `sInf` of an
empty or unbounded set. Registers are ordered `B × (R × (A × C))`, with `R` the paper's `A′`;
positive dimensions are `Fin (k + 1)`, with no bound. Side-information is one state `ψ`, used in
`n` i.i.d. copies, and the only communication is one forward message. Rates are in qubits,
entropies in bits, `fidelity` is squared, block lengths are `n ≥ 1`. Nonemptiness of `A` and `B`
follows from `IsDensityMatrix ρ`. -/
theorem theorem_1 {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Mat (A × B)) (hρ : IsDensityMatrix ρ) :
    IsGLB {Q : ℝ | ∃ r c : ℕ, ∃ ψ : Mat (B × (Fin (r + 1) × (A × Fin (c + 1)))),
        IsSideInformation ρ ψ ∧ IsAchievableRate ψ Q} (squashed ρ) := by sorry

end EntanglementParadigm
