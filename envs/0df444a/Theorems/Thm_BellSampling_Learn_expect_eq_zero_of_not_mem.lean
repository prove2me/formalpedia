-- Prove2me | Theorems.Thm_BellSampling_Learn_expect_eq_zero_of_not_mem
-- name    : BellSampling.Learn.expect_eq_zero_of_not_mem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:47.685195+00:00
-- url     : https://prove2.me/theorems/70e1e794-9559-4487-8bb5-a36140ca7795
-- title:
--   Learning stabilizer states, p. 2 — ⟨ψ|σ_t|ψ⟩ = 0 for every t ∉ T
-- statement:
--   Let $\psi$ be an $n$-qubit stabilizer state and $t\in\{0,1\}^{2n}$ a string with $t\notin T(\psi)$, that is, $\psi$ is not an eigenvector of $\sigma_t$. Then
--   $$\langle\psi|\sigma_t|\psi\rangle=\sum_x\overline{\psi(x)}\,(\sigma_t\psi)(x)=0.$$
--
--   Together with $|\langle\psi|\sigma_t|\psi\rangle|=1$ for $t\in T(\psi)$, this says that the expectation values of Pauli matrices in a stabilizer state are $0$ or of modulus $1$, which is what makes the Bell-sampling distribution uniform on a coset of $T$.
--
--   **Formalization Note** The page writes "for all Pauli matrices $M\notin G$"; read literally this fails for $M=-g$ with $g\in G$. It is stated here for strings outside $T$, i.e. Paulis not in $G$ up to a phase, which is the reading the argument uses.
-- source:
--   Montanaro, Learning stabilizer states by Bell sampling, arXiv:1707.04012v2, p. 2, Learning stabilizer states, "⟨ψ|M|ψ⟩ = 0 for all Pauli matrices M ∉ G"

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
open StabilizerRank

namespace BellSampling.Learn
theorem expect_eq_zero_of_not_mem {n : ℕ} (ψ : QState n) (hψ : IsStabilizerState ψ)
    (t : PStr n) (ht : t ∉ stabSet ψ) :
    ∑ x, star (ψ x) * ((sigma t).mulVec ψ) x = 0 := by sorry
end BellSampling.Learn
