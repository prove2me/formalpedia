-- Prove2me | Theorems.Thm_DiscreteEnergy_limits_of_energy_recursions
-- name    : DiscreteEnergy.limits_of_energy_recursions
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T10:51:46.694323+00:00
-- url     : https://prove2.me/theorems/262d1452-0be3-454a-86f2-737c09b97c43
-- title:
--   Rates forced by a pair of discrete energy recursions
-- statement:
--   Let $s>0$ and $\alpha>3$ be real numbers and let $\theta,\ d,\ e\colon\mathbb N\to\mathbb R$
--   be three nonnegative sequences. Assume that for every $n\in\mathbb N$ they satisfy the two
--   inequalities
--
--   $$
--   \frac{2s}{\alpha-1}(n+\alpha+1)^{2}\,\theta_{n+1}
--    +(\alpha-1)\,e_{n+1}
--    +\frac{2s}{\alpha-1}\bigl((\alpha-3)(n+2)+(\alpha-2)^{2}\bigr)\theta_{n}
--   \;\le\;
--   \frac{2s}{\alpha-1}(n+\alpha)^{2}\,\theta_{n}+(\alpha-1)\,e_{n}
--   $$
--
--   and
--
--   $$
--   2s\,\theta_{n+1}+d_{n+1}\;\le\;2s\,\theta_{n}
--    +\Bigl(\frac{n+1}{n+\alpha+1}\Bigr)^{2}d_{n}.
--   $$
--
--   Then all three of the following hold:
--
--   $$
--   (n+\alpha)^{2}\theta_{n}\xrightarrow[n\to\infty]{}0,
--   \qquad
--   (n+\alpha)^{2}d_{n}\xrightarrow[n\to\infty]{}0,
--   \qquad
--   e_{n}\ \text{converges to a finite limit.}
--   $$
--
--   The two hypotheses are the shape a discrete Lyapunov argument leaves behind. The first is an
--   *energy* inequality: a quantity built from $\theta$ and $e$ decreases from step $n$ to step
--   $n+1$, and the decrease comes with a nonnegative surplus proportional to $\theta_n$ whose
--   coefficient is positive exactly because $\alpha>3$. The second is a *shift* inequality for a
--   second quantity $d$, damped by the factor $\bigl((n+1)/(n+\alpha+1)\bigr)^2<1$. Neither
--   hypothesis says anything about where the sequences come from.
--
--   What the statement isolates is that these two inequalities alone already force the
--   $o(n^{-2})$ rates: no algorithm, no function, no space enters. In the convergence analysis of
--   inertial and accelerated first-order methods — where $\theta_n$ is an objective gap, $d_n$ a
--   squared distance to a minimizer, and $e_n$ an energy — this is the step where the recursions
--   are turned into rates, and it is a long argument involving a telescoping sum, a summability
--   argument and a non-summability argument against the harmonic series. Stated on its own it can
--   be applied wherever such a pair of recursions has been established, so the work of deriving
--   the recursions stays with the method at hand and the limit argument is done once.
--
--   **Formalization Note.** The three sequences are `θ`, `dd` and `ez`; nonnegativity is `hθ`,
--   `hdd` and `hez`; the energy and shift inequalities are `hE` and `hS`. The conclusion is a
--   conjunction of three statements, the first two `Tendsto (fun n => ((n:ℝ) + α) ^ 2 * ·) atTop
--   (𝓝 0)` and the third `∃ l, Tendsto ez atTop (𝓝 l)`. The casts `((n : ℝ) + α)` keep the index
--   in `ℕ` while the arithmetic happens in `ℝ`.
-- source:
--   The limit argument behind the $o(k^{-2})$ rates for inertial first-order methods with friction parameter $\alpha>3$. Carved verbatim, and identically, out of two accepted proofs that each derive it inline: NesterovFB.Weak.theorem_3, https://prove2.me/submissions/e3454a9c-3502-4c6b-9794-7eebefc4332c (lines 422-557), and NesterovFB.Rates.theorem_1, https://prove2.me/submissions/842bba92-1894-4b7e-9e8c-de15dbe6d45f (lines 365-500).

import Mathlib

open Filter Topology NNReal
open InnerProductSpace

theorem DiscreteEnergy.limits_of_energy_recursions (s α : ℝ) (hs : 0 < s) (hα : 3 < α) (θ dd ez : ℕ → ℝ)
    (hθ : ∀ n, 0 ≤ θ n) (hdd : ∀ n, 0 ≤ dd n) (hez : ∀ n, 0 ≤ ez n)
    (hE : ∀ n : ℕ, 2 * s / (α - 1) * ((n:ℝ) + α + 1) ^ 2 * θ (n + 1) + (α - 1) * ez (n + 1)
        + 2 * s / (α - 1) * ((α - 3) * ((n:ℝ) + 2) + (α - 2) ^ 2) * θ n ≤
        2 * s / (α - 1) * ((n:ℝ) + α) ^ 2 * θ n + (α - 1) * ez n)
    (hS : ∀ n : ℕ, 2 * s * θ (n + 1) + dd (n + 1) ≤
        2 * s * θ n + (((n:ℝ) + 1) / ((n:ℝ) + α + 1)) ^ 2 * dd n) :
    Tendsto (fun n : ℕ => ((n:ℝ) + α) ^ 2 * θ n) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ((n:ℝ) + α) ^ 2 * dd n) atTop (𝓝 0) ∧
    ∃ l, Tendsto ez atTop (𝓝 l) := by sorry
