-- Prove2me | Theorems.Thm_DirectFidelity_State_well_conditioned_m_le
-- name    : DirectFidelity.State.well_conditioned_m_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:52.971042+00:00
-- url     : https://prove2.me/theorems/772a13c3-165f-4d44-bed7-6a6fcebe1ac6
-- title:
--   p. 2 — for $\alpha$-well-conditioned $\rho$, $m_i \le 1 + 2\log(2/\delta)/(\alpha^2\ell\varepsilon^2)$
-- statement:
--   Let $\rho$ be a pure state on $n$ qubits which is well-conditioned with parameter $\alpha>0$: for every Pauli label $k$, either $\mathrm{tr}(\rho W_k) = 0$ or $|\mathrm{tr}(\rho W_k)|\ge\alpha$. Let $\varepsilon>0$, $0<\delta<1$, $\ell\ge1$. Then for every label $k$ with $\chi_\rho(k)\ne0$ (every label the sampling (3) can produce), the copy number (6) satisfies, with certainty,
--   $$m_i \le 1 + \frac{2\log(2/\delta)}{\alpha^2\ell\varepsilon^2}.$$
--
--   For stabilizer states ($\alpha = 1$) this makes the number of copies independent of the system size.
--
--   **Formalization Note.** The hypothesis $\delta<1$ is added as in (18), so that $\log(2/\delta)>0$.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 2, §Well-conditioned states

import Mathlib
import Definitions.Def_DirectFidelity_State_Setting

namespace DirectFidelity.State

theorem well_conditioned_m_le (n ℓ : ℕ) (ρ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ) (α : ℝ)
    (hα : 0 < α) (hwc : IsWellConditioned ρ α) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hℓ : 0 < ℓ) (k : P n) (hk : chi ρ k ≠ 0) :
    (mDFE ρ ε δ ℓ k : ℝ) ≤ 1 + 2 * Real.log (2 / δ) / (α ^ 2 * (ℓ : ℝ) * ε ^ 2) := by sorry

end DirectFidelity.State
