-- Prove2me | Theorems.Thm_FamousTheorems_digamma_one_eq_neg_euler_gamma_6c
-- name    : FamousTheorems.digamma_one_eq_neg_euler_gamma_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:46:20.632295+00:00
-- url     : https://prove2.me/theorems/cda23ba6-36af-47a1-9f33-6efa6fb36f35
-- title:
--   The digamma function at 1 equals −γ
-- statement:
--   **The digamma function at $1$.** Let $\psi=\Gamma'/\Gamma$ be the digamma function. Then
--   $$\psi(1)=-\gamma,$$
--   where $\gamma=\lim_{n\to\infty}\big(1+\frac12+\dots+\frac1n-\log n\big)$ is the Euler–Mascheroni constant. Equivalently, $\Gamma'(1)=-\gamma$.
--
--   Together with the recurrence $\psi(x+1)=\psi(x)+1/x$, this gives $\psi(n+1)=H_n-\gamma$ for the harmonic numbers $H_n$. This is one of the standard ways the Euler–Mascheroni constant appears in analysis.
--
--   **Formalization note.** Mathlib's `Complex.digamma_one`. `Complex.digamma` is the logarithmic derivative of the complex Gamma function, and `Real.eulerMascheroniConstant` is $\gamma$, cast to $\mathbb C$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Complex.digamma_one`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem digamma_one_eq_neg_euler_gamma_6c : Complex.digamma 1 = -(Real.eulerMascheroniConstant : ℂ) := by sorry

end FamousTheorems
