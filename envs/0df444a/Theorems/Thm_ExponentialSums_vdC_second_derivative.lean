-- Prove2me | Theorems.Thm_ExponentialSums_vdC_second_derivative
-- name    : ExponentialSums.vdC_second_derivative
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T10:18:30.370179+00:00
-- url     : https://prove2.me/theorems/1038fb61-45dc-46e6-9a1c-862d2aa8430c
-- title:
--   Van der Corput's second-derivative test
-- statement:
--   **Van der Corput's second-derivative test.**
--
--   Let $f$ be real valued on the integers of $(a,b]$, and write
--   $g(n) = f(n+1) - f(n)$ for its first differences, so that
--   $g(n+1) - g(n)$ is the second difference of $f$ at $n$ — the discrete analogue of $f''$.
--   Suppose that throughout the range the second difference is of a fixed size $\lambda > 0$ up to a
--   bounded factor $c \ge 1$:
--
--   $$\lambda \;\le\; g(n+1) - g(n) \;\le\; c\,\lambda \qquad (a < n < b).$$
--
--   Then the exponential sum satisfies
--
--   $$\left\| \sum_{a < n \le b} e\bigl(f(n)\bigr) \right\|
--   \;\le\; 8\left( c\,(b-a)\,\sqrt{\lambda} \;+\; \frac{1}{\sqrt{\lambda}} \right),
--   \qquad e(x) = e^{2\pi i x}.$$
--
--   The bound exhibits the characteristic van der Corput trade-off. The first term grows with the
--   length of the range but shrinks as the curvature $\lambda$ decreases; the second does the
--   opposite. Optimising over $\lambda$ — balancing the two terms at
--   $\lambda \asymp 1/(b-a)$ — yields the familiar estimate of size $\sqrt{b-a}$, a genuine
--   saving over the trivial bound $b - a$.
--
--   This is the second of van der Corput's two classical tools, the companion to the
--   Kusmin–Landau inequality. Where Kusmin–Landau requires the *first* derivative of $f$ to stay
--   away from the integers, the second-derivative test only requires the *second* derivative to be
--   of a controlled size, and so applies to functions such as $f(n) = t\log n$ that arise in
--   estimating the Riemann zeta function on vertical lines.
--
--   **Formalization note.** Everything is stated discretely on the differences of $f$, so no
--   differentiability is assumed; $e(x)$ is written out as `Complex.exp (2πi x)`. The absolute
--   constant is $8$.
-- source:
--   Classical; see Graham & Kolesnik, *van der Corput's Method of Exponential Sums*, Theorem 2.2, and Titchmarsh, *The Theory of the Riemann Zeta-Function*, §5.9. Lean proof extracted from `Salt/ExpSum/VdCorput2.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace ExponentialSums

theorem vdC_second_derivative {f : ℕ → ℝ} {a b : ℕ} {lam c : ℝ}
    (hab : a ≤ b) (hlam : 0 < lam) (hc : 1 ≤ c)
    (h2nd_lb : ∀ n, a < n → n < b →
        lam ≤ (f (n + 1 + 1) - f (n + 1)) - (f (n + 1) - f n))
    (h2nd_ub : ∀ n, a < n → n < b →
        (f (n + 1 + 1) - f (n + 1)) - (f (n + 1) - f n) ≤ c * lam) :
    ‖∑ n ∈ Finset.Ioc a b, Complex.exp (((2 * Real.pi * f n : ℝ) : ℂ) * Complex.I)‖
      ≤ 8 * (c * ((b : ℝ) - a) * Real.sqrt lam + 1 / Real.sqrt lam) := by sorry

end ExponentialSums
