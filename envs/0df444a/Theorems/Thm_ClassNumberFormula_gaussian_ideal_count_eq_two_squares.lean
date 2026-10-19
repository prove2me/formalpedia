-- Prove2me | Theorems.Thm_ClassNumberFormula_gaussian_ideal_count_eq_two_squares
-- name    : ClassNumberFormula.gaussian_ideal_count_eq_two_squares
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:52:46.595451+00:00
-- url     : https://prove2.me/theorems/9fa70632-6070-4b86-b1e1-d25f279c3a64
-- title:
--   $K=\mathbb Q(i)$: the coefficients of $\zeta_K$ count sums of two squares
-- statement:
--   Let $K$ be a quadratic number field containing a square root of $-1$, that is, $K \cong \mathbb Q(i)$, whose ring of integers is the Gaussian integers. Then for every $n\ge1$ the $n$-th coefficient of $\zeta_K$, the number of ideals of norm $n$, is
--   $$\#\{\mathfrak a \subseteq \mathcal O_K : N(\mathfrak a) = n\} = \#\{(a,b)\in\mathbb Z^2 : a > 0,\ b \ge 0,\ a^2 + b^2 = n\}.$$
--
--   The right-hand side is one quarter of the number $r_2(n)$ of representations of $n$ as a sum of two squares of integers. This makes precise the source's remark that the coefficient is "essentially the number of representations of $n$ as a sum of two squares of nonnegative integers".
--
--   **Formalization Note** The source's "essentially" is made exact by counting pairs with $a > 0$, $b \ge 0$ (one representative per unit class $\{\pm1,\pm i\}$); counting pairs of non-negative integers instead would overcount, e.g. for $n = 1$.
-- source:
--   Wikipedia, "Class number formula" (revision oldid=1366411311), https://en.wikipedia.org/w/index.php?title=Class_number_formula&oldid=1366411311, section "Proof", second paragraph ("The n-th coefficient of the Dirichlet series is essentially the number of representations of n as a sum of two squares")

import Mathlib
open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real

namespace ClassNumberFormula

theorem gaussian_ideal_count_eq_two_squares (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (hi : ∃ i : K, i ^ 2 = -1) (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} =
      Nat.card {p : ℤ × ℤ // 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 = n} := by sorry

end ClassNumberFormula
