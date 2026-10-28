-- Prove2me | Theorems.Thm_DirectFidelity_State_prob_normalized
-- name    : DirectFidelity.State.prob_normalized
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:43.654428+00:00
-- url     : https://prove2.me/theorems/733c3d87-9193-40a1-b09d-dcbf3c45c7ea
-- title:
--   Footnote [6], p. 4 — $\sum_k \chi_\rho(k)^2 = \mathrm{tr}(\rho^2) = 1$ for pure $\rho$
-- statement:
--   Let $\rho$ be a pure state on $n$ qubits. Then the importance-sampling weights $\Pr(k) = \chi_\rho(k)^2$ of (3) sum to one:
--   $$\sum_k \chi_\rho(k)^2 = \mathrm{tr}(\rho^2) = 1 .$$
--
--   So (3) is a probability distribution on the $d^2$ Pauli labels exactly when $\rho$ is pure; this is footnote [6].
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 4, footnote [6]

import Mathlib
import Definitions.Def_DirectFidelity_State_Setting

namespace DirectFidelity.State

theorem prob_normalized (n : ℕ) (ρ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ) :
    ∑ k : P n, prob ρ k = ((ρ * ρ).trace).re ∧ ((ρ * ρ).trace).re = 1 := by sorry

end DirectFidelity.State
