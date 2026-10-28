-- Prove2me | Theorems.Thm_DirectFidelity_State_eq_2
-- name    : DirectFidelity.State.eq_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:41.088241+00:00
-- url     : https://prove2.me/theorems/c976ea5f-cde8-4e7d-bf01-935fe9fa76b1
-- title:
--   (2), p. 1 — $\mathrm{tr}(\rho\sigma) = \sum_k \chi_\rho(k)\chi_\sigma(k)$
-- statement:
--   Let $\rho$ and $\sigma$ be Hermitian $d\times d$ matrices, $d = 2^n$, and let $\chi_\rho(k) = \mathrm{tr}(\rho W_k/\sqrt d)$ be the characteristic function over the $d^2$ Pauli operators $W_k$. Then
--   $$\mathrm{tr}(\rho\sigma) = \sum_{k}\chi_\rho(k)\,\chi_\sigma(k).$$
--
--   This is the Pauli-basis expansion of the Hilbert–Schmidt inner product: the normalized Pauli operators $W_k/\sqrt d$ form an orthonormal basis of the Hermitian matrices. It is what makes the importance-sampling estimator unbiased.
--
--   **Formalization Note.** The paper applies (2) to states; the statement is proved for all Hermitian $\rho,\sigma$, which contains that case. Traces are real parts of complex traces (real for Hermitian matrices).
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 1, §Fidelity Estimation, (2)

import Mathlib
import Definitions.Def_DirectFidelity_State_Setting

namespace DirectFidelity.State

theorem eq_2 (n : ℕ) (ρ σ : Matrix (Q n) (Q n) ℂ) (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ((ρ * σ).trace).re = ∑ k : P n, chi ρ k * chi σ k := by sorry

end DirectFidelity.State
