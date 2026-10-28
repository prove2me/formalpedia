-- Prove2me | Theorems.Thm_DirectFidelity_State_eq_1
-- name    : DirectFidelity.State.eq_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:46.816022+00:00
-- url     : https://prove2.me/theorems/b7a78f63-2f6f-4242-9bce-f029c705972b
-- title:
--   (1), p. 1 — for pure $\rho$, $\big(\mathrm{tr}[(\sqrt\rho\,\sigma\sqrt\rho)^{1/2}]\big)^2 = \mathrm{tr}(\rho\sigma)$
-- statement:
--   Let $\rho$ be a pure state and $\sigma$ an arbitrary state (density operator) on $\mathbb C^d$, $d = 2^n$. Then the Uhlmann fidelity of $\rho$ and $\sigma$ equals the overlap $\mathrm{tr}(\rho\sigma)$:
--   $$F(\rho,\sigma) = \Big(\mathrm{tr}\big[(\sqrt\rho\,\sigma\,\sqrt\rho)^{1/2}\big]\Big)^2 = \mathrm{tr}(\rho\sigma).$$
--
--   This identity is why the protocol's target is the linear quantity $\mathrm{tr}(\rho\sigma)$: for a pure desired state, estimating it is estimating the fidelity.
--
--   **Formalization Note.** Square roots of positive semidefinite matrices are Mathlib's continuous-functional-calculus `CFC.sqrt` under the matrix order (`open scoped MatrixOrder`); the trace of the outer square root is taken as a real part (it is real, the matrix being positive semidefinite).
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 1, §Fidelity Estimation, (1)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_DirectFidelity_State_Setting
open scoped MatrixOrder

namespace DirectFidelity.State

theorem eq_1 (n : ℕ) (ρ σ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ)
    (hσ : WildeQIT.IsDensityOperator σ) :
    ((CFC.sqrt (CFC.sqrt ρ * σ * CFC.sqrt ρ)).trace.re) ^ 2 = ((ρ * σ).trace).re := by sorry

end DirectFidelity.State
