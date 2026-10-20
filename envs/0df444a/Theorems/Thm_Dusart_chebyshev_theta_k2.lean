-- Prove2me | Theorems.Thm_Dusart_chebyshev_theta_k2
-- name    : Dusart.chebyshev_theta_k2
-- status  : Open
-- author  : @@bwdaugherty
-- created : 2026-10-16T21:33:22.072084+00:00
-- url     : https://prove2.me/theorems/e4af78fd-cb92-428c-ac7b-1afa1eeb4e3e
-- title:
--   Dusart's explicit Chebyshev estimate $|\theta(t)-t|\le t/(5\log^2t)$ for $t\ge3594641$
-- statement:
--   Let $\theta(t)=\sum_{p\le t}\log p$ be Chebyshev's function, the sum running over primes. For every real $t\ge 3594641$,
--
--   $$|\theta(t)-t|\le\frac{1}{5}\,\frac{t}{\log^2 t}.$$
--
--   This is the case $k=2$, $\eta_2=0.2$ of Dusart's explicit estimate (stated there with strict inequality). It is the only analytic input of Dusart's bound $\sum_{p\le x}1/p-\log\log x-B\le\frac{1}{10\log^2x}+\frac{4}{15\log^3x}$ for $x\ge10372$: that bound is proved on this platform from the present statement (`Dusart.reciprocal_primes_of_chebyshev`), so a proof of this estimate completes it unconditionally.
--
--   **Formalization Note** $\theta$ is Mathlib's `Chebyshev.theta`.
--
--   **Status note (2026-10-17)** The finite part $3594641\le t\le3584912847$ (`Dusart.chebyshev_theta_k2_finite`) is proved in Lean 4 in the release [Dusart v2.0.0, doi:10.5281/zenodo.23432990](https://doi.org/10.5281/zenodo.23432990); the open input is the part $t\ge3584912846$ (`Dusart.chebyshev_theta_k2_large`).
--
--   **Status note (2026-10-19)** In the release [Dusart v3.0.0, doi:10.5281/zenodo.23463154](https://doi.org/10.5281/zenodo.23463154), the finite part (`Dusart.chebyshev_theta_k2_finite`) is kernel-checked, and the part $t\ge3584912846$ (`Dusart.chebyshev_theta_k2_large`) is derived in Lean from the published table row $|\theta(t)-t|<0.15952\,t/\log^2t$ for $t>5\cdot10^6$ (Broadbent, Kadiri, Lumley, Ng and Wilk, Math. Comp. 90 (2021), Theorem 1 with $k=2$, Table 15, row $\log X_0=\log(5\cdot10^6)$) (`Dusart.chebyshev_theta_k2_large_of_bklnw`). That row is not formalized, and the finite certificate exceeds this platform's per-job limits, so this entry stays Open here.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 5.2 (table entry k = 2, η = 0.2, x ≥ 3 594 641); Dusart derives it from explicit estimates for ψ(x) − x (Proposition 3.2 and Tables 6.4–6.5 there).

import Mathlib.NumberTheory.Chebyshev

theorem Dusart.chebyshev_theta_k2 :
    ∀ t : ℝ, 3594641 ≤ t → |Chebyshev.theta t - t| ≤ (1 / 5) * t / Real.log t ^ 2 := by sorry
