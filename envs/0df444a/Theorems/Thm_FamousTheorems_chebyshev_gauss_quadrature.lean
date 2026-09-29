-- Prove2me | Theorems.Thm_FamousTheorems_chebyshev_gauss_quadrature
-- name    : FamousTheorems.chebyshev_gauss_quadrature
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:37:45.943132+00:00
-- url     : https://prove2.me/theorems/17e5c386-e256-4d32-91dd-2260ec3b8205
-- title:
--   Chebyshev–Gauss quadrature
-- statement:
--   **Chebyshev–Gauss quadrature.** Let $n\ge1$ and let $P$ be a real polynomial of degree less than $2n$. Then
--   $$\int_{-1}^{1}\frac{P(x)}{\sqrt{1-x^2}}\,dx=\frac{\pi}{n}\sum_{i=0}^{n-1}P\Big(\cos\frac{(2i+1)\pi}{2n}\Big).$$
--
--   The nodes $\cos\frac{(2i+1)\pi}{2n}$ are the zeros of the Chebyshev polynomial $T_n$. This is the Gauss quadrature rule for the Chebyshev weight, and it is exact up to the optimal degree $2n-1$. It is unusual in that the nodes and the weights, all equal to $\pi/n$, are given in closed form.
--
--   **Formalization note.** Mathlib's `Polynomial.Chebyshev.integral_eq_sumZeroes`. `Polynomial.Chebyshev.measureT` is Lebesgue measure on $(-1,1]$ with density $1/\sqrt{1-x^2}$, and `Polynomial.Chebyshev.sumZeroes n P` is the weighted sum on the right.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Polynomial.Chebyshev.integral_eq_sumZeroes`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem chebyshev_gauss_quadrature {n : ℕ} {P : Polynomial ℝ} (hn : n ≠ 0) (hP : P.degree < 2 * n) :
    ∫ x, P.eval x ∂Polynomial.Chebyshev.measureT = Polynomial.Chebyshev.sumZeroes n P := by sorry

end FamousTheorems
