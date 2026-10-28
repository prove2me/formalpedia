-- Prove2me | Theorems.Thm_DirectFidelity_State_eq_16
-- name    : DirectFidelity.State.eq_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:46.3956+00:00
-- url     : https://prove2.me/theorems/87d67c3b-2504-466b-86be-643a41bd6a29
-- title:
--   (16)–(17), p. 6 — $\Pr[|\tilde Y - Y| \ge t] \le 2\exp(-2t^2/C)$, $C = \sum_i\sum_{j\le m_i}(2c_i)^2$
-- statement:
--   Let $\rho$ be a pure state and $\sigma$ a state on $n$ qubits. Fix $\ell\ge1$ Pauli labels $k_1,\dots,k_\ell$ with $\chi_\rho(k_i)\ne0$ and positive copy numbers $m_1,\dots,m_\ell$. Measure $W_{k_i}$ on $m_i$ independent copies of $\sigma$, obtaining outcomes $A_{ij}\in\{1,-1\}$, and form $\tilde X_i = \frac{1}{m_i\sqrt d\,\chi_\rho(k_i)}\sum_{j=1}^{m_i}A_{ij}$ and $\tilde Y = \frac1\ell\sum_i\tilde X_i$. Let $Y = \frac1\ell\sum_i\chi_\sigma(k_i)/\chi_\rho(k_i)$ and
--   $$C = \sum_{i=1}^{\ell}\sum_{j=1}^{m_i}(2c_i)^2,\qquad c_i = \frac{1}{\ell\, m_i\sqrt d\,\chi_\rho(k_i)} .$$
--   Then for every $t > 0$,
--   $$\Pr\big[\,|\tilde Y - Y|\ge t\,\big] \le 2\exp(-2t^2/C).$$
--
--   This is Hoeffding's inequality for the finite-precision estimator: $\tilde Y$ is centred at $Y$ because $\mathbb E A_{ij} = \sqrt d\,\chi_\sigma(k_i)$.
--
--   **Formalization Note.** The page's free variable $\varepsilon$ in (16) is named $t$. The probability is over the Born-rule product law of the outcomes for the fixed labels. The copy numbers are an arbitrary positive vector, of which (6) is a special case.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 6, §Bounding the Failure Probabilities, (16)–(17)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_DirectFidelity_State_Setting

namespace DirectFidelity.State

theorem eq_16 (n ℓ : ℕ) (ρ σ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ)
    (hσ : WildeQIT.IsDensityOperator σ) (hℓ : 0 < ℓ) (ks : Fin ℓ → P n)
    (hks : ∀ i, chi ρ (ks i) ≠ 0) (m : Fin ℓ → ℕ) (hm : ∀ i, 0 < m i) (t : ℝ) (ht : 0 < t) :
    (outcomes σ ks m).real {A | t ≤ |Yt ρ ks m A - Y ρ σ ks|} ≤
      2 * Real.exp (-2 * t ^ 2 / Chof ρ ks m) := by sorry

end DirectFidelity.State
