-- Prove2me | Theorems.Thm_BBPSSW_Distill_werner_of_bilateral_invariant
-- name    : BBPSSW.Distill.werner_of_bilateral_invariant
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:46:09.912247+00:00
-- url     : https://prove2.me/theorems/4223730c-b1b2-4200-8c0c-3c5f44c53d19
-- title:
--   A random bilateral rotation turns every two-spin state into the Werner state of the same fidelity; rotationally symmetric states are Werner states, Eq. (4)
-- statement:
--   1. (The random bilateral rotation.) There are finitely many rotations $U_1,\dots,U_k\in SU(2)$ and probabilities $w_1,\dots,w_k\ge 0$ with $\sum_i w_i=1$ such that for every density matrix $M$ of two spin-$\tfrac12$ particles
--
--   $$\sum_i w_i\,(U_i\otimes U_i)\,M\,(U_i\otimes U_i)^\dagger = W_F,\qquad F=\langle\Psi^-|M|\Psi^-\rangle,$$
--
--   where $W_F$ is the Werner state of Eq. (4). That is, applying a randomly chosen bilateral rotation (the same random procedure for every input) turns $M$ into the rotationally symmetric mixture $W_F$ with the same $F$ as $M$.
--
--   2. (Rotationally symmetric states.) If a two-spin density matrix $\rho$ is invariant under every bilateral rotation, $(U\otimes U)\,\rho\,(U\otimes U)^\dagger=\rho$ for all $U\in SU(2)$, then $\rho=W_F$ with $F=\langle\Psi^-|\rho|\Psi^-\rangle$.
--
--   Differences from the source:
--   - reading: choosing a random SU(2) rotation (Haar) and applying it to both members of the pair transforms M into the rotationally symmetric mixture W_F (4) → some fixed finite probability distribution on SU(2), applied bilaterally, maps every density matrix M to W_F with F = ⟨Ψ−|M|Ψ−⟩; and every density matrix invariant under all bilateral SU(2) rotations equals W_F; reason: the Haar average is not formalized; a finite random choice is the paper's own alternative ("could also be achieved by choosing from a finite set of rotations"), and its output equals the Haar twirl's; the family is not pinned to {Bx, By, Bz, I}, for which uniform weights send Ψ+ to ½Ψ+ + ¼Φ+ + ¼Φ−, not to a Werner state
--   - encoding: F = ⟨Ψ−|M|Ψ−⟩ → the real part of ⟨Ψ−|M|Ψ−⟩; reason: the value is real for a density matrix
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, Eq. (4), p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_BBPSSW_Distill_bilateral
import Definitions.Def_BBPSSW_Distill_singletFidelity
import Definitions.Def_BBPSSW_Distill_wernerState

open QAlgorithms.Papers.Independent.Information100.P21 (QQ)
open scoped Matrix

namespace BBPSSW.Distill

/-- **A random bilateral rotation turns every two-spin state into the Werner state of the same
fidelity; rotationally symmetric states are Werner states, Eq. (4).**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, Eq. (4), p. 2: "the first step in our purification protocol is to have Alice and Bob
perform a random bilateral rotation on each shared pair, choosing a random SU(2) rotation
independently for each pair and applying it locally to both members of the pair … This
transforms the initial general two-spin mixed state M into a rotationally symmetric mixture
W_F = F·|Ψ−⟩⟨Ψ−| + (1−F)/3 |Ψ+⟩⟨Ψ+| + (1−F)/3 |Φ+⟩⟨Φ+| + (1−F)/3 |Φ−⟩⟨Φ−| (4)".

1. (The random bilateral rotation.) There is a probability distribution `w` on finitely many
   rotations `U₁, …, U_k ∈ SU(2)` such that, for every two-spin density matrix `M`, applying
   `U_i ⊗ U_i` with probability `w_i` gives the Werner state with the same singlet fidelity:
   `∑ᵢ wᵢ (Uᵢ ⊗ Uᵢ) M (Uᵢ ⊗ Uᵢ)† = W_F` with `F = ⟨Ψ⁻|M|Ψ⁻⟩`.
2. (Rotationally symmetric states.) If a two-spin density matrix `ρ` is invariant under every
   bilateral rotation, `(U ⊗ U) ρ (U ⊗ U)† = ρ` for all `U ∈ SU(2)`, then `ρ = W_F` with
   `F = ⟨Ψ⁻|ρ|Ψ⁻⟩`.

**Formalization Note.** The random SU(2) rotation is a random choice from a finite family of
SU(2) rotations with weights `w` (the paper notes the same result "could also be achieved by
choosing from a finite set of rotations"); the family is existentially quantified and fixed
before `M`, so one procedure serves every input. It is not pinned to `{Bx, By, Bz, I}`: with
uniform weights on that set, Ψ⁺ goes to ½Ψ⁺ + ¼Φ⁺ + ¼Φ⁻, not to a Werner state. The Haar
average itself is not formalized; clause 2 is the invariance characterization of "rotationally
symmetric". -/
theorem werner_of_bilateral_invariant :
    (∃ (k : ℕ) (U : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (w : Fin k → ℝ),
        (∀ i, U i ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧ (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
        ∀ M : Matrix QQ QQ ℂ, QAlgorithms.IsDensityMatrix M →
          ∑ i, ((w i : ℝ) : ℂ) • (bilateral (U i) * M * (bilateral (U i))ᴴ) =
            wernerState (singletFidelity M)) ∧
      ∀ ρ : Matrix QQ QQ ℂ, QAlgorithms.IsDensityMatrix ρ →
        (∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, bilateral U * ρ * (bilateral U)ᴴ = ρ) →
        ρ = wernerState (singletFidelity ρ) := by sorry

end BBPSSW.Distill
