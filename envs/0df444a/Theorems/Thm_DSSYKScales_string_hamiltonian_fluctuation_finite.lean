-- Prove2me | Theorems.Thm_DSSYKScales_string_hamiltonian_fluctuation_finite
-- name    : DSSYKScales.string_hamiltonian_fluctuation_finite
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T02:05:59.264146+00:00
-- url     : https://prove2.me/theorems/076bf7a0-ab7a-4e23-bc43-e7361e03a358
-- title:
--   $\langle H_s^2\rangle$ stays finite in the double-scaled limit: $H_s$ passes the test for $\mathcal A_s$
-- statement:
--   Let $(N_n,q_n)$ be double scaled with parameter $\lambda>0$ and let $\mathcal J\in\mathbb R$. Let $\langle H_s^2\rangle_{N,q}=\langle H_c^2\rangle_{N,q}/q^2$ be the second moment of the string Hamiltonian $H_s=H_c/q$ (eq. (3.7)). Then
--   $$\lim_{n\to\infty}\langle H_s^2\rangle_{N_n,q_n}=\frac{\mathcal J^2e^{-\lambda/2}}{\lambda}.$$
--
--   This is eq. (11.2), $\langle H_s^2\rangle=\mathcal J^2N/q^2=\mathcal J^2/\lambda$. Unlike $H_c$, the string Hamiltonian has finite fluctuations in the semiclassical limit, so it passes the test for membership in the string-scale algebra $\mathcal A_s$.
--
--   **Formalization Note** As for (11.1), the exact binomial count contributes the factor $e^{-\lambda/2}$ that the paper's approximation $\binom Nq\approx N^q/q!$ drops. The qualitative claim (a finite, nonzero limit for $\mathcal J\ne0$) is unchanged.
-- source:
--   L. Susskind, "De Sitter Space, Double-Scaled SYK, and the Separation of Scales in the Semiclassical Limit", arXiv:2209.09999v1 [hep-th] (2022), https://arxiv.org/abs/2209.09999, Section 11, p. 48, eq. (11.2); also eq. (3.7)

import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales
theorem string_hamiltonian_fluctuation_finite (N q : ℕ → ℕ) (lam J : ℝ)
    (hlim : IsDoubleScaledLimit N q lam) :
    Tendsto (fun n => stringHamiltonianSecondMoment (N n) (q n) J)
      atTop (𝓝 (J ^ 2 * Real.exp (-(lam / 2)) / lam)) := by sorry
end DSSYKScales
