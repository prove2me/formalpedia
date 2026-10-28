-- Prove2me | Theorems.Thm_DirectFidelity_State_expectation_X
-- name    : DirectFidelity.State.expectation_X
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:47.976342+00:00
-- url     : https://prove2.me/theorems/7c90cd80-4d8c-4ac5-bc68-044fdccdd28e
-- title:
--   p. 2 — $\mathbb E X = \mathrm{tr}(\rho\sigma)$ under $\Pr(k) = \chi_\rho(k)^2$
-- statement:
--   Let $\rho$ be a pure state and $\sigma$ a state on $n$ qubits. Draw a Pauli label $k$ with probability $\Pr(k) = \chi_\rho(k)^2$ and set $X = \chi_\sigma(k)/\chi_\rho(k)$. Then $X$ is an unbiased estimator of $\mathrm{tr}(\rho\sigma)$:
--   $$\mathbb E X = \sum_k \chi_\rho(k)^2\,\frac{\chi_\sigma(k)}{\chi_\rho(k)} = \mathrm{tr}(\rho\sigma).$$
--
--   **Formalization Note.** The expectation is the finite weighted sum over all $d^2$ labels. Labels with $\chi_\rho(k) = 0$ have weight $0$, so the junk value of $X$ there does not enter.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 2, §Fidelity Estimation, sentence after (4)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_DirectFidelity_State_Setting

namespace DirectFidelity.State

theorem expectation_X (n : ℕ) (ρ σ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ)
    (hσ : WildeQIT.IsDensityOperator σ) :
    ∑ k : P n, prob ρ k * X ρ σ k = ((ρ * σ).trace).re := by sorry

end DirectFidelity.State
