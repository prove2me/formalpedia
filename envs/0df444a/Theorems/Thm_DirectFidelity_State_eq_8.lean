-- Prove2me | Theorems.Thm_DirectFidelity_State_eq_8
-- name    : DirectFidelity.State.eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:47.993977+00:00
-- url     : https://prove2.me/theorems/8f55f499-7c5c-4ffd-99f8-607b42a9384b
-- title:
--   (8), p. 2 — given $k_1,\dots,k_\ell$ and $m_i$ as in (6), $\Pr[|\tilde Y - Y| \ge \varepsilon] \le \delta$
-- statement:
--   Let $\rho$ be a pure state and $\sigma$ a state on $n$ qubits, and $\varepsilon,\delta>0$. Fix any labels $k_1,\dots,k_\ell$, $\ell = \lceil 1/(\varepsilon^2\delta)\rceil$, with $\chi_\rho(k_i)\ne0$. Use $m_i$ copies of $\sigma$ for label $k_i$, with $m_i$ as in (6), measure $W_{k_i}$ on each, and form the estimate $\tilde Y$ of (7). Then
--   $$\Pr\big[\,|\tilde Y - Y|\ge\varepsilon\,\big]\le\delta ,$$
--   the probability being over the measurement outcomes.
--
--   This is the finite-precision half of the protocol's guarantee; together with (5) it gives the main result.
--
--   **Formalization Note.** The page states (8) after "Given any choice of $k_1,\dots,k_\ell$"; it is stated here for every fixed label tuple with all $\chi_\rho(k_i)\neq0$, the only tuples the sampling (3) produces with positive probability (at the others $\tilde X_i$ is undefined on the page and a junk value in Lean).
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 2, §Fidelity Estimation, (8); proof p. 6, (16)–(18)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_DirectFidelity_State_Setting

namespace DirectFidelity.State

theorem eq_8 (n : ℕ) (ρ σ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ)
    (hσ : WildeQIT.IsDensityOperator σ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (ks : Fin (ell ε δ) → P n) (hks : ∀ i, chi ρ (ks i) ≠ 0) :
    (outcomes σ ks (mVec ρ ε δ ks)).real
        {A | ε ≤ |Yt ρ ks (mVec ρ ε δ ks) A - Y ρ σ ks|} ≤ δ := by sorry

end DirectFidelity.State
