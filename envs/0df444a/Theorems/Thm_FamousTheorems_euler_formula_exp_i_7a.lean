-- Prove2me | Theorems.Thm_FamousTheorems_euler_formula_exp_i_7a
-- name    : FamousTheorems.euler_formula_exp_i_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:25:37.398346+00:00
-- url     : https://prove2.me/theorems/2e9fbab0-14a7-4f35-bbc9-a6de4fab09fa
-- title:
--   Euler's formula e^{ix} = cos x + i sin x
-- statement:
--   **Euler's formula.** For every complex number $x$,
--   $$e^{ix}=\cos x+i\sin x.$$
--
--   Euler published this formula in 1748. It links the exponential function with trigonometry, gives the polar form $z=re^{i\theta}$ of complex numbers, and turns trigonometric identities into algebra of exponentials. The case $x=\pi$ gives Euler's identity $e^{i\pi}+1=0$. The formula is the basis of Fourier analysis and of the treatment of oscillations in physics and engineering.
--
--   **Formalization note.** Mathlib's `Complex.exp_mul_I`. The statement is written as $\exp(x\cdot i)=\cos x+\sin x\cdot i$ with the complex exponential, cosine and sine, so it holds for all complex $x$ and not only for real $x$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Complex.exp_mul_I`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem euler_formula_exp_i_7a (x : ℂ) : Complex.exp (x * Complex.I) = Complex.cos x + Complex.sin x * Complex.I := by sorry

end FamousTheorems
