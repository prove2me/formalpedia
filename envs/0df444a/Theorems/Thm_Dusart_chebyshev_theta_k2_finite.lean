-- Prove2me | Theorems.Thm_Dusart_chebyshev_theta_k2_finite
-- name    : Dusart.chebyshev_theta_k2_finite
-- status  : Open
-- author  : @@bwdaugherty
-- created : 2026-10-16T21:58:18.781772+00:00
-- url     : https://prove2.me/theorems/302a7138-f59c-4188-b234-81b54a5bf65f
-- title:
--   Dusart's Chebyshev estimate on $[3594641,\,3584912847]$
-- statement:
--   For every real $t$ with $3594641\le t\le 3584912847$,
--
--   $$|\theta(t)-t|\le\frac{1}{5}\,\frac{t}{\log^2t},\qquad \theta(t)=\sum_{p\le t}\log p .$$
--
--   This is the finite part of Dusart's estimate (the case $k=2$, $\eta_2=0.2$ of his Theorem 5.2), up to just above $e^{22}\approx3584912846.13$. On this range Dusart uses exact values of $\theta$; his Table 6.4 gives only $\eta_2=0.2112>0.2$ on $[e^{21},e^{22}]$ from the analytic bounds. A proof is a finite computation over the primes up to $3.6\cdot10^9$.
--
--   **Formalization Note** $\theta$ is Mathlib's `Chebyshev.theta`.
--
--   **Status note (2026-10-17)** This statement is proved in Lean 4, kernel-checked with axioms `propext`, `Classical.choice`, `Quot.sound` only, in the release [Dusart v2.0.0, doi:10.5281/zenodo.23432990](https://doi.org/10.5281/zenodo.23432990), under the same name `Dusart.chebyshev_theta_k2_finite`. The proof is a kernel sieve certificate (3416 segments, 221 modules) whose memory and time needs exceed this platform's per-job limits, so it is not re-checked here; its checker and base range are proved on this platform as `ThetaCert.base`.
--
--   **Status note (2026-10-19)** The current release is [Dusart v3.0.0, doi:10.5281/zenodo.23463154](https://doi.org/10.5281/zenodo.23463154); its clean replay rebuilt the whole sieve certificate in a fresh Lean kernel environment (10 of 10 replay steps passed). The statement and proof of `Dusart.chebyshev_theta_k2_finite` are unchanged from v2.0.0, and for the reason above the entry stays Open here.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); finite range checked there with exact values of θ (Tables 6.1, 6.2, 6.6).; proved in Lean 4 in doi:10.5281/zenodo.23432990

import Mathlib.NumberTheory.Chebyshev

theorem Dusart.chebyshev_theta_k2_finite :
    ∀ t : ℝ, 3594641 ≤ t → t ≤ 3584912847 → |Chebyshev.theta t - t| ≤ (1 / 5) * t / Real.log t ^ 2 := by sorry
