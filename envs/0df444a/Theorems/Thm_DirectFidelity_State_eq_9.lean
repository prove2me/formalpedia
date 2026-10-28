-- Prove2me | Theorems.Thm_DirectFidelity_State_eq_9
-- name    : DirectFidelity.State.eq_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:46.290038+00:00
-- url     : https://prove2.me/theorems/851b28c8-4a4f-40d0-bf68-6b3f606814e0
-- title:
--   (9), p. 2 — $\mathbb E(m_i) = \sum_k \chi_\rho(k)^2 m_i \le 1 + \frac{2d}{\ell\varepsilon^2}\log(2/\delta)$
-- statement:
--   Let $\rho$ be a pure state on $n$ qubits ($d = 2^n$), $\varepsilon>0$, $0<\delta<1$ and $\ell\ge1$. If the label $k$ is drawn with probability $\chi_\rho(k)^2$ and $m(k) = \lceil\frac{2}{d\chi_\rho(k)^2\ell\varepsilon^2}\log(2/\delta)\rceil$ is the copy number (6), then
--   $$\mathbb E(m_i) = \sum_{k}\chi_\rho(k)^2\, m(k) \le 1 + \frac{2d}{\ell\varepsilon^2}\log(2/\delta).$$
--
--   This bounds the expected number of copies of $\sigma$ the protocol consumes per Pauli observable.
--
--   **Formalization Note.** The hypothesis $\delta<1$ is added, as in (18): it makes $\log(2/\delta)>0$; for large $\delta$ the right-hand side becomes negative while the left-hand side is $0$. Labels with $\chi_\rho(k) = 0$ carry weight $0$.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 2, §Fidelity Estimation, (9)

import Mathlib
import Definitions.Def_DirectFidelity_State_Setting

namespace DirectFidelity.State

theorem eq_9 (n ℓ : ℕ) (ρ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ) (ε δ : ℝ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hℓ : 0 < ℓ) :
    ∑ k : P n, prob ρ k * (mDFE ρ ε δ ℓ k : ℝ) ≤
      1 + 2 * dim n / ((ℓ : ℝ) * ε ^ 2) * Real.log (2 / δ) := by sorry

end DirectFidelity.State
