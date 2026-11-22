-- Prove2me | Theorems.Thm_BellSampling_Learn_conj_eq_sigmaZ
-- name    : BellSampling.Learn.conj_eq_sigmaZ
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:44.275047+00:00
-- url     : https://prove2.me/theorems/5ade6efb-76c3-435c-8b5d-3532272b1f5c
-- title:
--   Learning stabilizer states, p. 2 — |ψ*⟩ = σ₁₀^{⊗S}|ψ⟩ (up to an overall phase) for a stabilizer state
-- statement:
--   Let $\psi$ be an $n$-qubit stabilizer state. Then there are a subset $S\subseteq[n]$ and a complex number $c$ with $|c|=1$ such that the complex conjugate of $\psi$ in the computational basis satisfies
--   $$|\psi^*\rangle=c\,\sigma_{10}^{\otimes S}|\psi\rangle,$$
--   where $\sigma_{10}^{\otimes S}$ applies $\sigma_{10}=\mathrm{diag}(1,-1)$ to the qubits in $S$ and the identity elsewhere.
--
--   This is the step that turns Lemma 2 into eqn (1): conjugating a stabilizer state is the same as applying a diagonal Pauli to it.
--
--   **Formalization Note** The page writes the equality without a phase, but it derives it from a normal form that holds only up to an overall phase $e^{i\theta}$, which conjugates to $e^{-i\theta}$; the unit scalar $c$ records that phase. It does not affect eqn (1), where only $|\langle\psi|\sigma_r|\psi^*\rangle|$ enters.
-- source:
--   Montanaro, Learning stabilizer states by Bell sampling, arXiv:1707.04012v2, p. 2, Learning stabilizer states, "Hence |ψ∗⟩ = σ10^{⊗S}|ψ⟩"

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
open StabilizerRank

namespace BellSampling.Learn
theorem conj_eq_sigmaZ {n : ℕ} (ψ : QState n) (hψ : IsStabilizerState ψ) :
    ∃ S : Finset (Fin n), ∃ c : ℂ, ‖c‖ = 1 ∧
      (fun x => star (ψ x)) = c • (sigma (zStr S)).mulVec ψ := by sorry
end BellSampling.Learn
