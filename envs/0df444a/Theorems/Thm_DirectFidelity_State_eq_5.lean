-- Prove2me | Theorems.Thm_DirectFidelity_State_eq_5
-- name    : DirectFidelity.State.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:51.738147+00:00
-- url     : https://prove2.me/theorems/d2f39fcf-f252-480d-9f08-00898dcb40b6
-- title:
--   (5), p. 2 — with $\ell = \lceil 1/(\varepsilon^2\delta)\rceil$ i.i.d. labels, $\Pr[|Y - \mathrm{tr}(\rho\sigma)| \ge \varepsilon] \le \delta$
-- statement:
--   Let $\rho$ be a pure state and $\sigma$ a state on $n$ qubits, and let $\varepsilon,\delta > 0$. Draw $\ell = \lceil 1/(\varepsilon^2\delta)\rceil$ Pauli labels $k_1,\dots,k_\ell$ independently from $\Pr(k) = \chi_\rho(k)^2$, and set $Y = \frac1\ell\sum_{i=1}^\ell \chi_\sigma(k_i)/\chi_\rho(k_i)$. Then
--   $$\Pr\big[\,|Y - \mathrm{tr}(\rho\sigma)| \ge \varepsilon\,\big] \le \delta .$$
--
--   This is the guarantee of the ideal, infinite-precision estimator: a number of Pauli observables independent of the system size suffices.
--
--   **Formalization Note.** The probability is written out as the finite sum $\sum \prod_{i}\Pr(k_i)$ over the label tuples $(k_1,\dots,k_\ell)$ in the event. Tuples containing a label with $\chi_\rho(k_i) = 0$ have weight $0$.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 2, §Fidelity Estimation, (5); proof p. 6, (15)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_DirectFidelity_State_Setting

namespace DirectFidelity.State

theorem eq_5 (n : ℕ) (ρ σ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ)
    (hσ : WildeQIT.IsDensityOperator σ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∑ ks ∈ Finset.univ.filter
        (fun ks : Fin (ell ε δ) → P n => ε ≤ |Y ρ σ ks - ((ρ * σ).trace).re|),
      ∏ i, prob ρ (ks i) ≤ δ := by sorry

end DirectFidelity.State
