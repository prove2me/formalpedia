-- Prove2me | Theorems.Thm_Complex_exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add
-- name    : Complex.exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/1f036420-0dc3-5070-b263-769ccdceae14
-- title:
--   Local normal form of the germ |1-e^z|²log|1-e^z|
-- statement:
--   Write $z(x,\theta) = x/2 + 2\pi i\theta$ for $(x,\theta) \in \mathbb{R}\times\mathbb{R}$, put $s(x,\theta) = x^2/4 + 4\pi^2\theta^2$, and let $S = \{(x,\theta) : |\theta| < 1/2\}$. The assertion is the existence of two real-valued functions $a, b$ on $\mathbb{R}\times\mathbb{R}$ with the following five properties. First, $a$ and $b$ are both $C^\infty$ on $S$ (in the sense of `ContDiffOn ℝ ⊤`). Secondly, $a(x,\theta) > 0$ at every point of $S$. Thirdly, for every $(x,\theta) \in S$ one has the identity $$\bigl|1 - e^{z(x,\theta)}\bigr|^2 \log\bigl|1 - e^{z(x,\theta)}\bigr| = a(x,\theta)\,\bigl(s(x,\theta)\log s(x,\theta)\bigr) + s(x,\theta)\,b(x,\theta),$$ the logarithms being Mathlib's `Real.log`, so that $\log 0 = 0$ and both sides vanish at $(0,0)$. Fourthly, for every $(x,\theta)$ in the whole plane, $e^{z(x,\theta)} = 1$ holds if and only if $x = 0$ and $\theta$ is an integer. Fifthly, the function $(x,\theta) \mapsto |1 - e^{z(x,\theta)}|^2 \log|1 - e^{z(x,\theta)}|$ is itself $C^\infty$ on the open set where $e^{z(x,\theta)} \neq 1$.
--
--   This exhibits the singularity of the kink germ $|1-e^z|^2\log|1-e^z|$ along the strip $|\theta|<1/2$ as a smooth positive multiple of the model germ $s\log s$ in $s = |z|^2$ plus a remainder vanishing to second order, together with the exact location of the singular points and smoothness away from them. It is the local input to the two-dimensional Fourier decay estimate [`MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le`](thm.html#MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le), which is its only user.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Complex.exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add :
    ∃ a b : ℝ × ℝ → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) a {p : ℝ × ℝ | |p.2| < 1 / 2} ∧
      ContDiffOn ℝ (⊤ : ℕ∞) b {p : ℝ × ℝ | |p.2| < 1 / 2} ∧
      (∀ p : ℝ × ℝ, |p.2| < 1 / 2 → 0 < a p) ∧
      (∀ p : ℝ × ℝ, |p.2| < 1 / 2 →
        ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖ ^ 2 *
            Real.log ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖ =
          a p * ((p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2) *
              Real.log (p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2)) +
            (p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2) * b p) ∧
      (∀ p : ℝ × ℝ,
        Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ)) = 1 ↔
          p.1 = 0 ∧ ∃ k : ℤ, p.2 = k) ∧
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × ℝ =>
          ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖ ^ 2 *
            Real.log ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖)
        {p : ℝ × ℝ | Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ)) ≠ 1} := by sorry
