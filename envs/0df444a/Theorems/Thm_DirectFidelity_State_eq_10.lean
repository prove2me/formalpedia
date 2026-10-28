-- Prove2me | Theorems.Thm_DirectFidelity_State_eq_10
-- name    : DirectFidelity.State.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:53.89014+00:00
-- url     : https://prove2.me/theorems/8d9cbffe-a3b4-4e86-8c98-78e9a9393f68
-- title:
--   (10), p. 2 — $\mathbb E(m) \le 1 + \frac{1}{\varepsilon^2\delta} + \frac{2d}{\varepsilon^2}\log(2/\delta)$
-- statement:
--   Let $\rho$ be a pure state on $n$ qubits ($d=2^n$), $\varepsilon>0$ and $0<\delta<1$. With $\ell = \lceil1/(\varepsilon^2\delta)\rceil$ labels drawn independently from $\Pr(k) = \chi_\rho(k)^2$ and copy numbers $m_i$ as in (6), the total number of copies $m = \sum_{i=1}^\ell m_i$ satisfies
--   $$\mathbb E(m)\le 1 + \frac{1}{\varepsilon^2\delta} + \frac{2d}{\varepsilon^2}\log(2/\delta).$$
--
--   **Formalization Note.** The expectation is the finite sum over label tuples weighted by $\prod_i\Pr(k_i)$. The hypothesis $\delta<1$ is added as in (9).
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 2, §Fidelity Estimation, (10)

import Mathlib
import Definitions.Def_DirectFidelity_State_Setting

namespace DirectFidelity.State

theorem eq_10 (n : ℕ) (ρ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ) (ε δ : ℝ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∑ ks : Fin (ell ε δ) → P n, (∏ i, prob ρ (ks i)) * (∑ i, (mVec ρ ε δ ks i : ℝ)) ≤
      1 + 1 / (ε ^ 2 * δ) + 2 * dim n / ε ^ 2 * Real.log (2 / δ) := by sorry

end DirectFidelity.State
