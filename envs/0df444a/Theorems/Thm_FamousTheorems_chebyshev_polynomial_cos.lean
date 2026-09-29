-- Prove2me | Theorems.Thm_FamousTheorems_chebyshev_polynomial_cos
-- name    : FamousTheorems.chebyshev_polynomial_cos
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:06.609248+00:00
-- url     : https://prove2.me/theorems/242be4aa-e9fc-4cb9-b3e7-51e32b889011
-- title:
--   Chebyshev polynomials: T_n(cos θ) = cos(nθ)
-- statement:
--   **Chebyshev polynomials: $T_n(\cos\theta)=\cos(n\theta)$.** For every integer $n$ and every complex number $\theta$,
--   $$T_n(\cos\theta)=\cos(n\theta),$$
--   where $T_n$ is the Chebyshev polynomial of the first kind.
--
--   This identity characterises the Chebyshev polynomials. They express $\cos n\theta$ as a polynomial in $\cos\theta$. It gives their zeros and extrema and their orthogonality with respect to $1/\sqrt{1-x^2}$. It also makes them the optimal polynomials in minimax approximation (Chebyshev's equioscillation).
--
--   **Formalization note.** Mathlib's `Polynomial.Chebyshev.T_complex_cos`. `Polynomial.Chebyshev.T ℂ n` is defined for all integers $n$ by $T_0=1$, $T_1=X$, $T_{n+2}=2XT_{n+1}-T_n$, extended to negative $n$ by $T_{-n}=T_n$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Polynomial.Chebyshev.T_complex_cos`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem chebyshev_polynomial_cos (θ : ℂ) (n : ℤ) : (Polynomial.Chebyshev.T ℂ n).eval (Complex.cos θ) = Complex.cos (n * θ) := by sorry

end FamousTheorems
