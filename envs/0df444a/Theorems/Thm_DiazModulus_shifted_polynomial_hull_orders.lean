-- Prove2me | Theorems.Thm_DiazModulus_shifted_polynomial_hull_orders
-- name    : DiazModulus.shifted_polynomial_hull_orders
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-16T13:59:13.596637+00:00
-- url     : https://prove2.me/theorems/bf29ff12-d2bb-498d-8123-688a1fae9100
-- title:
--   Trailing degrees and degrees in the span of X^(k−1), X^k, X^(k+1) and two polynomials supported at the two ends
-- statement:
--   Let $K$ be a field, $2 \leq m \leq k$, $Q_1 \neq 0$ with trailing degree $k + m$ and degree $2k$, and $Q_2$ with non-zero constant term and degree $k - m$. Every non-zero $f$ in the span of $X^{k-1}, X^k, X^{k+1}, Q_1, Q_2$ has trailing degree in $\{0, k - 1, k, k + 1, k + m\}$ and degree in $\{k - m, k - 1, k, k + 1, 2k\}$.
--
--   **Proof.** Write $f = c_1X^{k-1} + c_2X^k + c_3X^{k+1} + \alpha Q_1 + \beta Q_2$. As $k - 1 \geq 1$, only $Q_2$ has a constant term; $Q_1$ is supported in $[k+m, 2k]$ with $k + m \geq k + 2$, and $Q_2$ in $[0, k - m]$ with $k - m \leq k - 2$. Reading off coefficients, the trailing degree is $0$ if $\beta \neq 0$, else the first of $k - 1, k, k + 1$ with $c_i \neq 0$, else $k + m$; the degree is $2k$ if $\alpha \neq 0$, else the last of $k + 1, k, k - 1$ with $c_i \neq 0$, else $k - m$.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. R16 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 16 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem shifted_polynomial_hull_orders (K : Type*) [Field K] (k m : ℕ) (hm : 2 ≤ m) (hmk : m ≤ k)
    (Q₁ Q₂ : K[X]) (hQ₁ : Q₁ ≠ 0) (hQ₁t : Q₁.natTrailingDegree = k + m)
    (hQ₁d : Q₁.natDegree = 2 * k) (hQ₂ : Q₂.coeff 0 ≠ 0) (hQ₂d : Q₂.natDegree = k - m)
    (f : K[X]) (hf : f ∈ Submodule.span K ({X ^ (k - 1), X ^ k, X ^ (k + 1), Q₁, Q₂} : Set K[X]))
    (hf0 : f ≠ 0) :
    f.natTrailingDegree ∈ ({0, k - 1, k, k + 1, k + m} : Finset ℕ) ∧
      f.natDegree ∈ ({k - m, k - 1, k, k + 1, 2 * k} : Finset ℕ) := by
  sorry

end DiazModulus
