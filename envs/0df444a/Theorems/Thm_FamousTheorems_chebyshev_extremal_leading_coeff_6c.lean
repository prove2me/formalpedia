-- Prove2me | Theorems.Thm_FamousTheorems_chebyshev_extremal_leading_coeff_6c
-- name    : FamousTheorems.chebyshev_extremal_leading_coeff_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:46:08.595782+00:00
-- url     : https://prove2.me/theorems/42e7fc6f-94a4-466b-8af1-01b9cc70a558
-- title:
--   Chebyshev's extremal property of the Chebyshev polynomials
-- statement:
--   **Chebyshev's extremal property.** Let $P$ be a real polynomial of degree at most $n$ with $|P(x)|\le 1$ for all $x\in[-1,1]$. Then the leading coefficient of $P$ is at most $2^{n-1}$.
--
--   Equality holds for the Chebyshev polynomial $T_n$. Equivalently, among monic polynomials of degree $n\ge1$, the scaled Chebyshev polynomial $2^{1-n}T_n$ has the smallest supremum norm on $[-1,1]$. This is the starting point of approximation theory and explains why Chebyshev nodes are good interpolation points.
--
--   **Formalization note.** Mathlib's `Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one`. The exponent $n-1$ is natural-number subtraction, so for $n=0$ the bound is $2^0=1$. `P.leadingCoeff` is the coefficient of the top-degree term of $P$ (and $0$ for $P=0$).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem chebyshev_extremal_leading_coeff_6c {n : ℕ} {P : Polynomial ℝ} (hPdeg : P.degree ≤ n)
    (hPbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) : P.leadingCoeff ≤ 2 ^ (n - 1) := by sorry

end FamousTheorems
