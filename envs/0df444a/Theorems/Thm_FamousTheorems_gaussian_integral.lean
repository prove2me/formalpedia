-- Prove2me | Theorems.Thm_FamousTheorems_gaussian_integral
-- name    : FamousTheorems.gaussian_integral
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:47.178984+00:00
-- url     : https://prove2.me/theorems/03b11e25-aaff-4ae2-b2ab-7c620678952d
-- title:
--   The Gaussian integral
-- statement:
--   **The Gaussian integral.** For $b>0$,
--   $$\int_{-\infty}^{\infty}e^{-bx^2}\,dx=\sqrt{\frac\pi b}.$$
--
--   For $b=1$ this is $\int e^{-x^2}dx=\sqrt\pi$. The Gaussian integral normalises the normal distribution, gives $\Gamma(\tfrac12)=\sqrt\pi$, and is the prototype for Gaussian integrals in physics and probability.
--
--   **Formalization note.** Mathlib's `integral_gaussian`, stated for all real `b` without hypothesis. For $b\le0$ the integrand is not integrable, so Mathlib's Bochner integral is $0$, and `Real.sqrt` of a nonpositive number is also $0$. The identity is therefore trivially true there, and its content is the case $b>0$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `integral_gaussian`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem gaussian_integral (b : ℝ) : ∫ x : ℝ, Real.exp (-b * x ^ 2) = Real.sqrt (Real.pi / b) := by sorry

end FamousTheorems
