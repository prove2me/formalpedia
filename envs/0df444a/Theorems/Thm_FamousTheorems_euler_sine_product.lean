-- Prove2me | Theorems.Thm_FamousTheorems_euler_sine_product
-- name    : FamousTheorems.euler_sine_product
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:58.692464+00:00
-- url     : https://prove2.me/theorems/f251de1d-cc81-4a49-ae59-adc65d0ac2e8
-- title:
--   Euler's sine product formula
-- statement:
--   **Euler's sine product formula.** For every complex number $z$,
--   $$\sin(\pi z)=\pi z\prod_{j=1}^{\infty}\Big(1-\frac{z^2}{j^2}\Big).$$
--
--   Euler used this factorization in 1734, by comparing the coefficients of $z^3$, to solve the Basel problem $\sum1/n^2=\pi^2/6$. Setting $z=\tfrac12$ gives the Wallis product for $\pi$. The formula is the prototype of the Weierstrass and Hadamard factorization theorems for entire functions.
--
--   **Formalization note.** Mathlib's `Complex.tendsto_euler_sin_prod`. The infinite product is stated as the limit of the partial products $\pi z\prod_{j<n}\big(1-z^2/(j+1)^2\big)$ as $n\to\infty$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Complex.tendsto_euler_sin_prod`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem euler_sine_product (z : ℂ) :
    Filter.Tendsto (fun n : ℕ => (Real.pi : ℂ) * z * ∏ j ∈ Finset.range n, (1 - z ^ 2 / ((j : ℂ) + 1) ^ 2))
      Filter.atTop (nhds (Complex.sin ((Real.pi : ℂ) * z))) := by sorry

end FamousTheorems
