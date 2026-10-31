-- Prove2me | Theorems.Thm_AccelSGDGrowth_moment_bounds_schedule
-- name    : AccelSGDGrowth.moment_bounds_schedule
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:05.48474+00:00
-- url     : https://prove2.me/theorems/55fcf749-387f-4654-beda-918ad3bf7a0c
-- title:
--   Moment bounds (b) — second moments under the schedule of Theorem 5.1 (corrected: $a_k/A_k=\sqrt{m\mathcal L}\,\eta_k$ for $k\ge2$)
-- statement:
--   For all $0<m\le\mathcal L$, $\delta\ge0$ and $\alpha>0$ there is a sequence $(B_k)$, depending only on $m,\mathcal L,\delta,\alpha$, such that in every setting of Theorem 5.1 (any dimension, probability space, $f\in\mathcal F(m,\mathcal L)$, $\sigma^2\ge0$, weights and run) with minimizer $x_\star$, writing $D_0=\mathbb E\|\nabla f(x_1)\|^2$, for every $k\ge1$:
--   $$
--   \mathbb E\|x_k-x_\star\|^2\le B_k(D_0+\sigma^2),\qquad \mathbb E\|\nabla f(x_k)\|^2\le B_k(D_0+\sigma^2),\qquad \mathbb EV_{k+1}\le B_k(D_0+\sigma^2).
--   $$
--
--   When $\alpha>\gamma_1$, the schedule gives $r_k>1/\gamma_4$ on the finitely many steps $\gamma_4/\alpha\le k<\gamma_4/\gamma_1$, where the recursion (5.2) is not available; these bounds control those steps in the proof of Theorem 5.1.
--
--   Differences from the source:
--   - reading: no statement on the page; the proof of Theorem 5.1 applies (5.2), which requires r_k ≤ 1/γ₄, for every k → explicit moment bounds with constants uniform over the instance; reason: for α > γ₁ the condition r_k ≤ 1/γ₄ fails on finitely many steps, which these bounds cover
--   - correction: a_k/A_k = √(mL) η_k (for all k ≥ 1) → imposed for k ≥ 2 only; reason: A_1 = a_1 gives a_1/A_1 = 1, while √(mL)η_1 = 1/(2(1+δ)√κ) ≤ 1/2 in the first phase; e.g. m = L = 1, δ = 0, α = 1 admits no positive weight sequence satisfying the printed condition; a_1 > 0 stays free and only ratios enter the scheme
--   - generalization: γ₄/α an integer (p.22, 'for simplifying our presentation') → any α > 0, with k₀ = ⌈γ₄/α⌉, the first k with αk ≥ γ₄; reason: for integer γ₄/α, k₀ = γ₄/α and every formula specializes to the printed one
--   - generalization: noise ε_k drawn from ε(x_k), a family satisfying (1.7), with (2.5) derived from it → the conditional form (2.5) assumed directly: g_k is 𝒢_{k+1}-measurable, E[ε_k | 𝒢_k] = 0 and E[‖ε_k‖² | 𝒢_k] ≤ δ‖∇f(x_k)‖² + σ² a.s.; reason: every oracle of Definition 1.1 yields (2.5), so the paper's setting is a special case
--   - generalization: initial point x_1 left unspecified → x_1 random, 𝒢_1-strongly measurable with E‖x_1‖² < ∞; y_1 free; z_1 = 0 not assumed; reason: a deterministic x_1 is a special case; y_1 enters only through A_0/A_1 = 0, and (4.6a) at k = 1 forces z_1 = 0
--   - encoding: E‖ε_k‖² used without comment → ‖ε_k‖² integrable, as part of the growth condition; reason: Lean's conditional expectation of a non-integrable function is 0; the condition only excludes cases where the paper's expectations are undefined
--   - encoding: f ∈ F(m, L), m-strongly convex with condition number κ = L/m → 0 < m and m ≤ L as hypotheses; reason: strong convexity and κ = L/m need m > 0; (1.2) forces m ≤ L whenever d ≥ 1, so only the trivial case d = 0 is affected
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, implicit in the proofs of Theorem 4.1, pp.18–19, and Theorem 5.1, p.24 (no label)

import Definitions.Def_AccelSGDGrowth_TailDAMSetting
import Definitions.Def_AccelSGDGrowth_gapV

open MeasureTheory

namespace AccelSGDGrowth

universe u

/-- Moment bounds, part (b): second moments under the schedule of Theorem 5.1. No label in the
paper; implicit in the proof of Chen, Na, Kolar, arXiv:2006.06782v4, Theorem 4.1, pp.18–19, and
needed in §5 when `α > γ₁` (then `r_k > 1/γ₄` on the finitely many steps `γ₄/α ≤ k < γ₄/γ₁`, where
the recursion (5.2) is not available).

For all `0 < m ≤ L`, `δ ≥ 0`, `α > 0` there is a sequence `B : ℕ → ℝ`, depending only on
`m, L, δ, α`, such that in every setting of Theorem 5.1 (`TailDAMSetting`, any dimension, any
probability space, any `f`, `σ²`, weights and run) with minimizer `x⋆`, writing
`D₀ = E‖∇f(x_1)‖²`, for every `k ≥ 1`:
`E‖x_k − x⋆‖² ≤ B_k (D₀ + σ²)`, `E‖∇f(x_k)‖² ≤ B_k (D₀ + σ²)` and `E V_{k+1} ≤ B_k (D₀ + σ²)`.

**Formalization Note.** `∃ B` is placed before the dimension, the space, `f`, `σ²` and the run, so
`B` is uniform over them. -/
theorem moment_bounds_schedule :
    ∀ m L δ α : ℝ, 0 < m → m ≤ L → 0 ≤ δ → 0 < α →
    ∃ B : ℕ → ℝ, ∀ (d : ℕ) (Ω : Type u) (mΩ : MeasurableSpace Ω) (μ : Measure Ω),
      IsProbabilityMeasure μ →
      ∀ (𝒢 : Filtration ℕ mΩ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (sig2 : ℝ) (a η : ℕ → ℝ)
        (x y z g : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (xstar : EuclideanSpace ℝ (Fin d)),
      TailDAMSetting μ 𝒢 f m L δ sig2 α a η x y z g → IsMinOn f Set.univ xstar →
      ∀ k : ℕ, 1 ≤ k →
        ∫ ω, ‖x k ω - xstar‖ ^ 2 ∂μ ≤
          B k * ((∫ ω, ‖gradient f (x 1 ω)‖ ^ 2 ∂μ) + sig2) ∧
        ∫ ω, ‖gradient f (x k ω)‖ ^ 2 ∂μ ≤
          B k * ((∫ ω, ‖gradient f (x 1 ω)‖ ^ 2 ∂μ) + sig2) ∧
        ∫ ω, gapV f m a (fun j => x j ω) (fun j => y j ω) (fun j => g j ω) xstar (k + 1) ∂μ ≤
          B k * ((∫ ω, ‖gradient f (x 1 ω)‖ ^ 2 ∂μ) + sig2) := by sorry

end AccelSGDGrowth
