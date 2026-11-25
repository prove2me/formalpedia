-- Prove2me | Theorems.Thm_Complex_sum_mul_pow_isBigO_pow_iff_norm_le
-- name    : Complex.sum_mul_pow_isBigO_pow_iff_norm_le
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:25:43.889613+00:00
-- url     : https://prove2.me/theorems/618bcfd6-969f-59ed-a655-8fd8d5801412
-- title:
--   Growth of exponential polynomials: $\sum_{z \in s} c_z z^m = O(R^m)$ as $m \to \infty$ iff $|z| \le R$ for every $z \in s$ with $c_z \neq 0$
-- statement:
--   Let $s$ be a finite set of complex numbers, let $c : \mathbb C \to \mathbb C$ be a coefficient function and let $R \ge 0$ be a real number. Consider the exponential polynomial (generalized power sum)
--
--   $$a_m = \sum_{z \in s} c_z\, z^m, \qquad m = 0, 1, 2, \dots$$
--
--   Then $a_m = O(R^m)$ as $m \to \infty$ (that is, $|a_m| \le C R^m$ for some constant $C$ and all large $m$) if and only if $|z| \le R$ for every $z \in s$ whose coefficient $c_z$ is nonzero.
--
--   The direction "if" is the triangle inequality. The content is "only if": no cancellation between the terms can hide a base of modulus larger than $R$ with a nonzero coefficient. For example, $2^m + (-2)^m$ is not $O(1)$ (it is $2^{m+1}$ for even $m$), and $a_m = 2^m$ is not $O(1^m)$.
--
--   Role: this is the Rankin-type step that turns a bound $\sum_i \alpha_i^m = O(R^m)$ on power sums of eigenvalues (traces of Frobenius or of powers of a Hecke operator) into the bound $|\alpha_i| \le R$ on each eigenvalue.
--
--   **Formalization Note**: `Asymptotics.IsBigO Filter.atTop f g` is Mathlib's $f = O(g)$ along $m \to \infty$ for sequences indexed by $m : \mathbb N$; the comparison sequence is the real sequence $R^m$. `‖z‖` is the complex absolute value. The coefficient function $c$ is defined on all of $\mathbb C$, but only its values on $s$ enter.
-- source:
--   R. A. Rankin, Contributions to the theory of Ramanujan's function tau(n) and similar arithmetical functions, Proc. Cambridge Philos. Soc. 35 (1939); P. Deligne, La conjecture de Weil I, Publ. Math. IHES 43 (1974), Section 1.7 (the limit argument); standard fact on exponential polynomials / linear recurrences

import Mathlib

set_option autoImplicit false

theorem Complex.sum_mul_pow_isBigO_pow_iff_norm_le (s : Finset ℂ) (c : ℂ → ℂ) (R : ℝ) (hR : 0 ≤ R) :
    Asymptotics.IsBigO Filter.atTop (fun m : ℕ => ∑ z ∈ s, c z * z ^ m) (fun m : ℕ => R ^ m) ↔
      ∀ z ∈ s, c z ≠ 0 → ‖z‖ ≤ R := by
  sorry
