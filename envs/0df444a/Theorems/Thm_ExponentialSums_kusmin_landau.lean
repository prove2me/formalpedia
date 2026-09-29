-- Prove2me | Theorems.Thm_ExponentialSums_kusmin_landau
-- name    : ExponentialSums.kusmin_landau
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T07:58:47.880595+00:00
-- url     : https://prove2.me/theorems/f8587cf4-0c93-4ea1-89a0-32bbdfca7d22
-- title:
--   The Kusmin–Landau inequality
-- statement:
--   **The Kusmin–Landau inequality.** Let $f$ be real valued on the integers of $(a,b]$ and write
--   $g(n) = f(n+1) - f(n)$ for its consecutive differences. Suppose that on that range $g$ is
--
--   * **monotone** (non-decreasing), and
--   * **uniformly away from the integers**, in the sense that for some integer $m$ and some
--     $0 < \delta \le 1/2$ one has $m + \delta \le g(n) \le m + 1 - \delta$.
--
--   Then the exponential sum over the range is bounded by a quantity depending only on $\delta$:
--
--   $$\left\| \sum_{a < n \le b} e\bigl(f(n)\bigr) \right\| \le \frac{1}{\delta},
--   \qquad e(x) = e^{2\pi i x}.$$
--
--   The bound is **independent of the length $b - a$ of the range**, which is what makes the
--   inequality useful: it converts a hypothesis about the *derivative* of $f$ staying away from
--   integers into genuine cancellation in the sum.
--
--   The proof is by Abel summation against the telescoping weight $w(n) = (1 - e(g(n)))^{-1}$.
--   Monotonicity of $g$ makes the weights $w(n)$ vary monotonically in argument, so the
--   differences $w(n+1) - w(n)$ telescope rather than accumulate, and the separation hypothesis
--   gives $\|1 - e(g(n))\| \ge 2\sin(\pi\delta) \ge 4\delta$, bounding each weight.
--
--   Kusmin–Landau is the first of the two classical van der Corput tools; the second is the
--   discrete second-derivative test. It is stated here discretely, directly on the differences
--   $g(n) = f(n+1) - f(n)$, so that no differentiability of $f$ is needed.
-- source:
--   Classical; see Graham & Kolesnik, *van der Corput's Method of Exponential Sums*, Lemma 2.1, and Iwaniec & Kowalski, *Analytic Number Theory*, §8.2. Lean proof extracted from `Salt/ExpSum/Kusmin.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey); the statement is restated here with the additive character written out as `Complex.exp (2πi x)`.

import Mathlib

namespace ExponentialSums

theorem kusmin_landau {f : ℕ → ℝ} {a b : ℕ} {δ : ℝ} {m : ℤ}
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hg_lb : ∀ n, a < n → n ≤ b → (m : ℝ) + δ ≤ f (n + 1) - f n)
    (hg_ub : ∀ n, a < n → n ≤ b → f (n + 1) - f n ≤ (m : ℝ) + 1 - δ)
    (hmono : ∀ n, a < n → n < b → f (n + 1) - f n ≤ f (n + 2) - f (n + 1)) :
    ‖∑ n ∈ Finset.Ioc a b,
        Complex.exp (((2 * Real.pi * f n : ℝ) : ℂ) * Complex.I)‖ ≤ 1 / δ := by sorry

end ExponentialSums
