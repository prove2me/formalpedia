-- Prove2me | Theorems.Thm_Dusart_chebyshev_theta_k2_large
-- name    : Dusart.chebyshev_theta_k2_large
-- status  : Open
-- author  : @@bwdaugherty
-- created : 2026-10-16T21:58:18.989754+00:00
-- url     : https://prove2.me/theorems/6beffd1a-8a12-47cc-a6af-b7880427fe93
-- title:
--   Dusart's Chebyshev estimate for $t\ge e^{22}$
-- statement:
--   For every real $t\ge 3584912846$ (just below $e^{22}$),
--
--   $$|\theta(t)-t|\le\frac{1}{5}\,\frac{t}{\log^2t},\qquad \theta(t)=\sum_{p\le t}\log p .$$
--
--   This is the analytic part of Dusart's estimate (Theorem 5.2, $k=2$, $\eta_2=0.2$). Dusart obtains it from bounds $|\theta(x)-x|<\varepsilon_\theta(b)\,x$ for $x\ge e^b$ (his Table 6.3, after Schoenfeld). These give $\eta_2\le0.1524$ on $[e^{22},e^{23}]$ and smaller values beyond (Tables 6.4–6.5), with an asymptotic bound for $x\ge e^{5000}$. Those bounds rest on explicit estimates for $\psi(x)-x$ from zero-free regions and zero computations of $\zeta$.
--
--   **Formalization Note** $\theta$ is Mathlib's `Chebyshev.theta`.
--
--   **Status note (2026-10-17)** With this statement, Dusart's bound for $\sum_{p\le x}1/p$ ($x\ge10372$) follows in Lean 4: the complementary finite range and the deduction are proved in the release [Dusart v2.0.0, doi:10.5281/zenodo.23432990](https://doi.org/10.5281/zenodo.23432990).
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); derived there from Table 6.3 (ε_θ(b)) and Tables 6.4–6.5 (η_2 column) for x ≥ e^22.

import Mathlib.NumberTheory.Chebyshev

theorem Dusart.chebyshev_theta_k2_large :
    ∀ t : ℝ, 3584912846 ≤ t → |Chebyshev.theta t - t| ≤ (1 / 5) * t / Real.log t ^ 2 := by sorry
