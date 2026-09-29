-- Prove2me | Theorems.Thm_FamousTheorems_riemann_zeta_laurent_euler_mascheroni_7b
-- name    : FamousTheorems.riemann_zeta_laurent_euler_mascheroni_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:22.803986+00:00
-- url     : https://prove2.me/theorems/7771bdd5-6422-4bc6-8a92-048fc20b0119
-- title:
--   ζ(s) − 1/(s − 1) → γ as s → 1
-- statement:
--   **The constant term of $\zeta$ at $s=1$ is the Euler–Mascheroni constant.** As $s\to1$ in $\mathbb C$ with $s\neq1$,
--   $$\zeta(s)-\frac1{s-1}\to\gamma,$$
--   where $\gamma=\lim_{n\to\infty}\big(1+\tfrac12+\dots+\tfrac1n-\log n\big)$ is the Euler–Mascheroni constant.
--
--   So the Laurent expansion of $\zeta$ at its pole is $\zeta(s)=\frac1{s-1}+\gamma+O(s-1)$. The higher coefficients are the Stieltjes constants. The formula connects $\gamma$ with the analytic theory of primes, for instance in Mertens' third theorem, and follows from comparing $\sum n^{-s}$ with $\int_1^\infty x^{-s}\,dx$.
--
--   **Formalization note.** Mathlib's `tendsto_riemannZeta_sub_one_div`. The limit is along the punctured neighbourhood filter `nhdsWithin 1 {1}ᶜ` of $1$ in $\mathbb C$, and `Real.eulerMascheroniConstant` is $\gamma$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `tendsto_riemannZeta_sub_one_div`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem riemann_zeta_laurent_euler_mascheroni_7b : Filter.Tendsto (fun s : ℂ => riemannZeta s - 1 / (s - 1)) (nhdsWithin 1 {1}ᶜ)
    (nhds (Real.eulerMascheroniConstant : ℂ)) := by sorry

end FamousTheorems
