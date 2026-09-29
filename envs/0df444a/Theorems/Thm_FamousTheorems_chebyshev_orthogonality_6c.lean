-- Prove2me | Theorems.Thm_FamousTheorems_chebyshev_orthogonality_6c
-- name    : FamousTheorems.chebyshev_orthogonality_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:46:22.671523+00:00
-- url     : https://prove2.me/theorems/88bdba96-0327-4de6-8aa6-b141c2655ef3
-- title:
--   Orthogonality of the Chebyshev polynomials
-- statement:
--   **Orthogonality of the Chebyshev polynomials.** For natural numbers $n\ne m$,
--   $$\int_{-1}^{1}T_n(x)\,T_m(x)\,\frac{dx}{\sqrt{1-x^2}}=0,$$
--   where $T_n$ is the Chebyshev polynomial of the first kind, defined by $T_n(\cos\theta)=\cos n\theta$.
--
--   The Chebyshev polynomials are the orthogonal polynomials for the weight $1/\sqrt{1-x^2}$ on $[-1,1]$. Through $x=\cos\theta$ this is the orthogonality of $\cos n\theta$ on $[0,\pi]$, which links Chebyshev expansions to Fourier cosine series. It underlies Chebyshev spectral methods and Gauss–Chebyshev quadrature.
--
--   **Formalization note.** Mathlib's `Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne`. `Polynomial.Chebyshev.measureT` is Lebesgue measure with density $1/\sqrt{1-x^2}$, restricted to $(-1,1]$. `Polynomial.Chebyshev.T ℝ n` is $T_n$ with real coefficients (Mathlib indexes it by integers, and $n$ is cast from $\mathbb N$).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem chebyshev_orthogonality_6c {n m : ℕ} (h : n ≠ m) :
    ∫ x, (Polynomial.Chebyshev.T ℝ n).eval x * (Polynomial.Chebyshev.T ℝ m).eval x
      ∂Polynomial.Chebyshev.measureT = 0 := by sorry

end FamousTheorems
