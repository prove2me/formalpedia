-- Prove2me | Theorems.Thm_EntanglementParadigm_eq_4_splitting
-- name    : EntanglementParadigm.eq_4_splitting
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:29:37.313064+00:00
-- url     : https://prove2.me/theorems/e229a832-d05c-443b-8c5e-3e00e98b910e
-- title:
--   Eq. (4), first equality: splittings of $E$ and channels on $E$ give the same values
-- statement:
--   Let $|\Psi\rangle_{ABE}$ be a unit vector on finite registers purifying $\rho_{AB}$. The values of $\tfrac12 I(A:B|C)$ over all splittings of the purifying system into $A'$ and $C$ coincide with the values of $\tfrac12 I(A:B|\Lambda(E))$ over all channels $\Lambda$ on $E$:
--
--   $$
--   \Bigl\{\tfrac12 I(A:B|C)_\psi : \psi \text{ side-information for } \rho_{AB}\Bigr\}
--   =\Bigl\{\tfrac12 I(A:B|\tilde E)_{(\mathrm{id}_{AB}\otimes\Lambda)(|\Psi\rangle\langle\Psi|)} : \Lambda:E\to\tilde E \text{ channel}\Bigr\}.
--   $$
--
--   Here $\psi$ ranges over pure states on $B\otimes A'\otimes A\otimes C$ with $AB$ marginal $\rho_{AB}$, and $A'$, $C$, $\tilde E$ over all finite nonzero registers. In particular the infima of the two sets agree, which is the first equality of Eq. (4): in the paper's words, $A'$ acts as the environment of a channel on $E$ whose output is $C$.
--
--   Differences from the source:
--   - generalization: equality of two infima → equality of the two sets of values; reason: equal sets have equal infima, so this specializes to the source's line, and no sInf enters
--   - reading: no statement on dimension → every register finite, with no bound on any dimension; reason: qubit counting, the entropies of Eq. (2) and the paper's references [4], [10] are finite-dimensional
--   - encoding: registers B, A′, A, C → ordered B × (R × (A × C)) with R the paper's A′; positive dimensions Fin (k + 1); reason: Lean convention, the order of Intakenext100.P75; same instances
--   - encoding: qubit rates and entropies with no stated base → logb 2 of the message dimension, von Neumann entropy in bits; reason: Eq. (2) equates a qubit rate with ½I, which fixes base 2
-- source:
--   J. Oppenheim, A paradigm for entanglement theory based on quantum communication, arXiv:0801.0458v1, Eq. (4), first equality, p.2

import Definitions.Def_EntanglementParadigm_IsSideInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Intakenext100.P75 (conditionedLastCMIBits discardReference)
open QAlgorithms.Papers.Independent.Dependency50.P19 (conditionalMutual)

namespace EntanglementParadigm

/-- Oppenheim, arXiv:0801.0458v1, Eq. (4), first equality, p.2: for a fixed purification
`|Ψ⟩_{ABE}` of `ρ_AB`, the values `½ I(A : B|C)` over all splittings of the purifying system into
`A′` and `C` are exactly the values `½ I(A : B|Λ(E))` over all channels `Λ` on `E`.

**Formalization Note.** Stated as an equality of sets of reals, which implies the equality of the
two infima of Eq. (4) and involves no `sInf`. Registers of a splitting are ordered
`B × (R × (A × C))`, with `R` the paper's `A′`, and positive dimensions are `Fin (k + 1)`. No
bound on any dimension is imposed. Entropies are in bits. Nonemptiness of the registers follows
from `‖Ψ‖ = 1`. -/
theorem eq_4_splitting {A B E : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E]
    (ρ : Mat (A × B)) (Ψ : EuclideanSpace ℂ ((A × B) × E)) (hΨ : ‖Ψ‖ = 1)
    (hpur : traceRight (pureDensity Ψ) = ρ) :
    {x : ℝ | ∃ r c : ℕ, ∃ ψ : Mat (B × (Fin (r + 1) × (A × Fin (c + 1)))),
        IsSideInformation ρ ψ ∧ x = conditionedLastCMIBits (discardReference ψ) / 2} =
      {x : ℝ | ∃ e : ℕ, 0 < e ∧ ∃ L : Superop E (Fin e), IsChannel L ∧
        x = conditionalMutual (idTensorSuperop L (pureDensity Ψ)) / 2} := by sorry

end EntanglementParadigm
