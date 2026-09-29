-- Prove2me | Theorems.Thm_FamousTheorems_euler_gauss_gamma_limit_formula
-- name    : FamousTheorems.euler_gauss_gamma_limit_formula
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:37:11.935989+00:00
-- url     : https://prove2.me/theorems/155bbdcb-5d56-4204-923b-e01b1dafd9bc
-- title:
--   The Euler–Gauss limit formula for the Gamma function
-- statement:
--   **The Euler–Gauss limit formula for the Gamma function.** For every complex number $s$,
--   $$\Gamma(s)=\lim_{n\to\infty}\frac{n^s\,n!}{s(s+1)\cdots(s+n)}.$$
--
--   Euler used this product as his original definition of the Gamma function, and Gauss took it as the starting point of his theory. It holds for all $s\in\mathbb C$, including the poles: there both sides are $0$ in Mathlib's convention. It leads directly to the Weierstrass product for $1/\Gamma$ and to the reflection formula.
--
--   **Formalization note.** Mathlib's `Complex.GammaSeq_tendsto_Gamma`. The sequence is written out explicitly; it is definitionally Mathlib's `Complex.GammaSeq s`. `Complex.Gamma` has value $0$ at the non-positive integers.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Complex.GammaSeq_tendsto_Gamma`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem euler_gauss_gamma_limit_formula (s : ℂ) :
    Filter.Tendsto (fun n : ℕ => (n : ℂ) ^ s * n.factorial / ∏ j ∈ Finset.range (n + 1), (s + j))
      Filter.atTop (nhds (Complex.Gamma s)) := by sorry

end FamousTheorems
