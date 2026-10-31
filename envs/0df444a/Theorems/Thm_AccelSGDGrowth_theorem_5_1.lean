-- Prove2me | Theorems.Thm_AccelSGDGrowth_theorem_5_1
-- name    : AccelSGDGrowth.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:34.875137+00:00
-- url     : https://prove2.me/theorems/93418c67-6ed9-4c4e-93ff-d0e0b1b2d16c
-- title:
--   Theorem 5.1 — tail-averaged DAM+ attains $\exp[-k/(2(1+\delta)\sqrt\kappa)]+\sigma^2\log k/k$ (corrected: $a_k/A_k$ for $k\ge2$; bias tail $D_0/k$, printed form for $\sigma^2>0$)
-- statement:
--   Consider DAM+ (4.6) under the growth condition (Definition 1.1) with $\delta\ge0$, for $f\in\mathcal F(m,\mathcal L)$, $0<m\le\mathcal L$, $\kappa=\mathcal L/m$. Let $\eta_k=r_k$ and $w_{k,t}$ be given by (5.4) with $\gamma_1=\sqrt{m\mathcal L}$, $\gamma_4=2\mathcal L(1+\delta)$ and any $\alpha>0$, let $a_k/A_k=\sqrt{m\mathcal L}\,\eta_k$ for $k\ge2$, and let $\bar x_k=\sum_{t=1}^kw_{k,t}x_t/W_k$. Write
--   $$
--   c=\frac1{2(1+\delta)\sqrt\kappa},\qquad D_0=\mathbb E\|\nabla f(x_1)\|^2,\qquad \mathrm{Gap}_k=\mathbb E\big[f(\bar x_k)-f(x_\star)\big].
--   $$
--   Then:
--
--   1. **(A) First phase.** For all $0<m\le\mathcal L$ and $\delta\ge0$ there is $C_1>0$ such that for every $\alpha>0$, every instance and every $k\ge1$ with $\alpha k<\gamma_4$:
--   $$
--   \mathrm{Gap}_k\le C_1\Big(D_0e^{-ck}+\frac{\sigma^2}{\alpha k}\Big).
--   $$
--   2. **(B) Second phase.** For all $0<m\le\mathcal L$, $\delta\ge0$ and $\alpha>0$ there is $C_2>0$ such that for every instance and every $k\ge1$ with $\alpha k\ge\gamma_4$:
--   $$
--   \mathrm{Gap}_k\le C_2\,\frac{D_0+\sigma^2\log k}{k}.
--   $$
--   3. **(C) The printed rate (5.12).** For every instance with $\sigma^2>0$ there is $C_3>0$ such that for all $k\ge1$:
--   $$
--   \mathrm{Gap}_k\le C_3\Big(\exp\Big[-\frac{k}{2(1+\delta)\sqrt\kappa}\Big]+\frac{\log k}{k}\,\sigma^2\Big).
--   $$
--
--   An instance is a dimension $d$, a probability space with filtration, $f$, $\sigma^2\ge0$, weights, step sizes and a run satisfying all of the above, together with the minimizer $x_\star$. The rate nearly matches the lower bound (5.1), $\Omega(\exp(-k/\sqrt\kappa)+\sigma^2/k)$, up to the factor $2(1+\delta)$ in the exponent and $\log k$ in the variance term, for every multiplicative noise level $\delta\ge0$.
--
--   **Formalization Note** $C_1$ is chosen before $\alpha$ and the instance, $C_2$ before the instance (it may depend on $\alpha$), and $C_3$ after the instance, as the page's $O$ ("for some positive constant $c$", p.5). The bounds hold for all $k\ge1$, not eventually.
--
--   Differences from the source:
--   - correction: a_k/A_k = √(mL) η_k (for all k ≥ 1) → imposed for k ≥ 2 only; reason: A_1 = a_1 gives a_1/A_1 = 1, while √(mL)η_1 = 1/(2(1+δ)√κ) ≤ 1/2 in the first phase; e.g. m = L = 1, δ = 0, α = 1 admits no positive weight sequence satisfying the printed condition; a_1 > 0 stays free and only ratios enter the scheme
--   - correction: (5.12): E[f(x̄_k) − f(x⋆)] = O(exp[−k/(2(1+δ)√κ)] + (log k/k)σ²) for every σ² ≥ 0 and α > 0 → three clauses: (A) first phase with C₁ free of α: Gap_k ≤ C₁(D₀e^{−ck} + σ²/(αk)); (B) second phase: Gap_k ≤ C₂(D₀ + σ² log k)/k; (C) the printed bound with an instance-dependent constant when σ² > 0; reason: the printed bound is false at σ² = 0: d = 1, f(x) = x²/2, m = L = 1, δ = 0, α = 2, x_1 = 1, ε ≡ 0 is admissible and gives f(x̄_k) = 1/(2k²), which is not O(e^{−k/2}); the bias tail D₀/k hidden by the O in (5.11) is kept in (B)
--   - generalization: γ₄/α an integer (p.22, 'for simplifying our presentation') → any α > 0, with k₀ = ⌈γ₄/α⌉, the first k with αk ≥ γ₄; reason: for integer γ₄/α, k₀ = γ₄/α and every formula specializes to the printed one
--   - generalization: noise ε_k drawn from ε(x_k), a family satisfying (1.7), with (2.5) derived from it → the conditional form (2.5) assumed directly: g_k is 𝒢_{k+1}-measurable, E[ε_k | 𝒢_k] = 0 and E[‖ε_k‖² | 𝒢_k] ≤ δ‖∇f(x_k)‖² + σ² a.s.; reason: every oracle of Definition 1.1 yields (2.5), so the paper's setting is a special case
--   - generalization: initial point x_1 left unspecified → x_1 random, 𝒢_1-strongly measurable with E‖x_1‖² < ∞; y_1 free; z_1 = 0 not assumed; reason: a deterministic x_1 is a special case; y_1 enters only through A_0/A_1 = 0, and (4.6a) at k = 1 forces z_1 = 0
--   - encoding: E‖ε_k‖² used without comment → ‖ε_k‖² integrable, as part of the growth condition; reason: Lean's conditional expectation of a non-integrable function is 0; the condition only excludes cases where the paper's expectations are undefined
--   - encoding: f ∈ F(m, L), m-strongly convex with condition number κ = L/m → 0 < m and m ≤ L as hypotheses; reason: strong convexity and κ = L/m need m > 0; (1.2) forces m ≤ L whenever d ≥ 1, so only the trivial case d = 0 is affected
--   - reading: O(·) 'for any k ≥ 1', with O defined by 'some positive constant c' (p.5) → explicit constants valid for every k ≥ 1; C₁ before α and the instance, C₂ before the instance, C₃ after it; reason: 'for any k ≥ 1' is a bound for all k, not eventually; the uniform constants of (A) and (B) are what the proof gives, and (C) is the page's instance-wise O
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, Theorem 5.1, (5.12), p.24

import Definitions.Def_AccelSGDGrowth_TailDAMSetting
import Definitions.Def_AccelSGDGrowth_tailAverage

open MeasureTheory

namespace AccelSGDGrowth

universe u

/-- Chen, Na, Kolar, arXiv:2006.06782v4, Theorem 5.1, p.24 (corrected). DAM+ (4.6) under the growth
condition (Definition 1.1) with `δ ≥ 0`, `r_k = η_k` and `w_{k,t}` from (5.4) with `γ₁ = √(mL)`,
`γ₄ = 2L(1+δ)` and any `α > 0`, `a_k/A_k = √(mL)η_k` (for `k ≥ 2`), and the tail average
`x̄_k = Σ_{t=1}^k w_{k,t}x_t / W_k`. Write `κ = L/m`, `c = 1/(2(1+δ)√κ)`, `D₀ = E‖∇f(x_1)‖²`,
`Gap_k = E[f(x̄_k) − f(x⋆)]`. Three clauses:

(A) first phase: for all `0 < m ≤ L`, `δ ≥ 0` there is `C₁ > 0` such that for every `α > 0`, every
    setting and every `k ≥ 1` with `αk < γ₄`: `Gap_k ≤ C₁ (D₀ e^{−ck} + σ²/(αk))`;
(B) second phase: for all `0 < m ≤ L`, `δ ≥ 0`, `α > 0` there is `C₂ > 0` such that for every setting
    and every `k ≥ 1` with `γ₄ ≤ αk`: `Gap_k ≤ C₂ (D₀ + σ² log k)/k`;
(C) the printed (5.12): for every setting with `σ² > 0` there is `C₃ > 0` such that for all `k ≥ 1`:
    `Gap_k ≤ C₃ (e^{−ck} + (log k / k) σ²)`.

**Formalization Note.** A "setting" is `TailDAMSetting` (any dimension `d`, any probability space with
filtration, any `f ∈ F(m, L)`, any `σ² ≥ 0`, weights, step sizes and run) together with the minimizer
`x⋆`. `C₁` is chosen before `α` and the setting, `C₂` before the setting (it may depend on `α`), and
`C₃` after the setting (the page's `O` with "some positive constant c", p.5). `O(·)` is read for all
`k ≥ 1`, not eventually. Corrections: `a_k/A_k = √(mL)η_k` is imposed for `k ≥ 2` (it is impossible at
`k = 1`), and the printed (5.12) is false at `σ² = 0` (for `d = 1`, `f = x²/2`, `α = 2`, `x_1 = 1`,
`f(x̄_k) = 1/(2k²)`), so (C) assumes `σ² > 0` and (B) carries the `1/k` bias tail. `γ₄/α` need not be
an integer. -/
theorem theorem_5_1 :
    (∀ m L δ : ℝ, 0 < m → m ≤ L → 0 ≤ δ →
      ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ (α : ℝ) (d : ℕ) (Ω : Type u) (mΩ : MeasurableSpace Ω) (μ : Measure Ω),
        IsProbabilityMeasure μ →
        ∀ (𝒢 : Filtration ℕ mΩ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (sig2 : ℝ) (a η : ℕ → ℝ)
          (x y z g : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (xstar : EuclideanSpace ℝ (Fin d)),
        TailDAMSetting μ 𝒢 f m L δ sig2 α a η x y z g → IsMinOn f Set.univ xstar →
        ∀ k : ℕ, 1 ≤ k → α * (k : ℝ) < 2 * L * (1 + δ) →
          ∫ ω, (f (tailAverage (2 * L * (1 + δ)) α (fun t => x t ω) k) - f xstar) ∂μ ≤
            C₁ * ((∫ ω, ‖gradient f (x 1 ω)‖ ^ 2 ∂μ) *
                Real.exp (-(1 / (2 * (1 + δ) * Real.sqrt (L / m)) * (k : ℝ))) +
              sig2 / (α * (k : ℝ)))) ∧
    (∀ m L δ α : ℝ, 0 < m → m ≤ L → 0 ≤ δ → 0 < α →
      ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ (d : ℕ) (Ω : Type u) (mΩ : MeasurableSpace Ω) (μ : Measure Ω),
        IsProbabilityMeasure μ →
        ∀ (𝒢 : Filtration ℕ mΩ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (sig2 : ℝ) (a η : ℕ → ℝ)
          (x y z g : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (xstar : EuclideanSpace ℝ (Fin d)),
        TailDAMSetting μ 𝒢 f m L δ sig2 α a η x y z g → IsMinOn f Set.univ xstar →
        ∀ k : ℕ, 1 ≤ k → 2 * L * (1 + δ) ≤ α * (k : ℝ) →
          ∫ ω, (f (tailAverage (2 * L * (1 + δ)) α (fun t => x t ω) k) - f xstar) ∂μ ≤
            C₂ * ((∫ ω, ‖gradient f (x 1 ω)‖ ^ 2 ∂μ) + sig2 * Real.log k) / (k : ℝ)) ∧
    (∀ (m L δ sig2 α : ℝ) (d : ℕ) (Ω : Type u) (mΩ : MeasurableSpace Ω) (μ : Measure Ω),
      IsProbabilityMeasure μ →
      ∀ (𝒢 : Filtration ℕ mΩ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (a η : ℕ → ℝ)
        (x y z g : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (xstar : EuclideanSpace ℝ (Fin d)),
      0 < m → m ≤ L → 0 < sig2 →
      TailDAMSetting μ 𝒢 f m L δ sig2 α a η x y z g → IsMinOn f Set.univ xstar →
      ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ k : ℕ, 1 ≤ k →
        ∫ ω, (f (tailAverage (2 * L * (1 + δ)) α (fun t => x t ω) k) - f xstar) ∂μ ≤
          C₃ * (Real.exp (-(1 / (2 * (1 + δ) * Real.sqrt (L / m)) * (k : ℝ))) +
            Real.log k / (k : ℝ) * sig2)) := by sorry

end AccelSGDGrowth
