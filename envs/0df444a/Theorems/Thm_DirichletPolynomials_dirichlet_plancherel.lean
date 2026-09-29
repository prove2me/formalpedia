-- Prove2me | Theorems.Thm_DirichletPolynomials_dirichlet_plancherel
-- name    : DirichletPolynomials.dirichlet_plancherel
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T09:25:43.879287+00:00
-- url     : https://prove2.me/theorems/49a66f78-40b5-454f-9324-419b5598c6b4
-- title:
--   A Plancherel identity for Dirichlet polynomials on a vertical line
-- statement:
--   **A Plancherel-type identity for Dirichlet polynomials.**
--
--   Let $F \subset \mathbb{N}$ be a finite set of indices, all at least $1$, let $b : \mathbb{N} \to
--   \mathbb{C}$ be coefficients, and fix $c > 0$. Consider the Dirichlet polynomial evaluated on the
--   vertical line $s = c + it$,
--
--   $$D(t) \;=\; \sum_{n \in F} \frac{b_n}{n^{\,c + it}}.$$
--
--   Then the weighted mean square of $D$ along that line has a **closed form as a double sum over
--   the coefficients**, with no integral remaining:
--
--   $$\int_{-\infty}^{\infty} \frac{|D(t)|^2}{c^2 + t^2}\,dt
--   \;=\; \frac{\pi}{c} \sum_{m \in F} \sum_{n \in F}
--   \frac{\operatorname{Re}\bigl(b_m \overline{b_n}\bigr)}{(mn)^{c}}\,
--   e^{-c\,\bigl|\log m - \log n\bigr|}.$$
--
--   The Cauchy weight $1/(c^2 + t^2)$ is what makes the identity exact rather than merely an
--   inequality: its Fourier transform is the two-sided exponential $\tfrac{\pi}{c}e^{-c|u|}$, and
--   the diagonal and off-diagonal contributions are separated by the quantity
--   $|\log m - \log n|$, the logarithmic distance between the two frequencies.
--
--   Identities of this shape are the starting point for mean-value estimates for Dirichlet
--   polynomials, where the off-diagonal terms are shown to be small and the diagonal $m = n$ gives
--   the main term $\tfrac{\pi}{c}\sum_{n \in F}|b_n|^2 n^{-2c}$. They are the technical engine
--   behind large-sieve and Halász-type bounds in analytic number theory.
--
--   **Formalization note.** The integral is Bochner integration over $\mathbb{R}$, and
--   $\operatorname{Re}(b_m \overline{b_n})$ is written with `starRingEnd`. The hypothesis
--   $1 \le n$ on $F$ ensures every $\log n$ is defined and non-negative.
-- source:
--   Classical; the Cauchy-weighted mean-value identity underlying Montgomery–Vaughan style large-sieve and Halász estimates, cf. Montgomery, *Topics in Multiplicative Number Theory*, and Iwaniec & Kowalski, *Analytic Number Theory*, §7. Lean proof extracted from `Salt/MR/HalaszContour.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace DirichletPolynomials

theorem dirichlet_plancherel (F : Finset ℕ) (b : ℕ → ℂ) {c : ℝ} (hc : 0 < c)
    (hF : ∀ n ∈ F, 1 ≤ n) :
    ∫ t : ℝ, ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 / (c ^ 2 + t ^ 2)
      = Real.pi / c * ∑ m ∈ F, ∑ n ∈ F,
          (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(c * |Real.log m - Real.log n|)) := by sorry

end DirichletPolynomials
