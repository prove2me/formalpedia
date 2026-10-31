-- Prove2me | Theorems.Thm_AccelSGDGrowth_jensen_theorem_5_1
-- name    : AccelSGDGrowth.jensen_theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:41.549583+00:00
-- url     : https://prove2.me/theorems/8350a704-cf93-4d2e-9c0a-98478640e6ce
-- title:
--   The Jensen step in the proof of Theorem 5.1 (corrected: $a_k/A_k=\sqrt{m\mathcal L}\,\eta_k$ for $k\ge2$)
-- statement:
--   In the setting of Theorem 5.1 ($\gamma_4=2\mathcal L(1+\delta)$), with $0<m\le\mathcal L$ and minimizer $x_\star$, for every $k\ge1$:
--   $$
--   \mathbb E\big[f(\bar x_k)-f(x_\star)\big]\le\frac1{W_k}\sum_{t=1}^kw_{k,t}\,\mathbb E\big[f(x_t)-f(x_\star)\big]\le\frac1{2mW_k}\sum_{t=1}^kw_{k,t}\,\mathbb E\|\nabla f(x_t)\|^2 .
--   $$
--   The first inequality is convexity of $f$ along the weighted average, the second is Lemma 2.1(a) at $x_\star$. It reduces Theorem 5.1 to Proposition 5.1 with $s_t=\mathbb E\|\nabla f(x_t)\|^2$.
--
--   Differences from the source:
--   - correction: a_k/A_k = √(mL) η_k (for all k ≥ 1) → imposed for k ≥ 2 only; reason: A_1 = a_1 gives a_1/A_1 = 1, while √(mL)η_1 = 1/(2(1+δ)√κ) ≤ 1/2 in the first phase; e.g. m = L = 1, δ = 0, α = 1 admits no positive weight sequence satisfying the printed condition; a_1 > 0 stays free and only ratios enter the scheme
--   - generalization: γ₄/α an integer (p.22, 'for simplifying our presentation') → any α > 0, with k₀ = ⌈γ₄/α⌉, the first k with αk ≥ γ₄; reason: for integer γ₄/α, k₀ = γ₄/α and every formula specializes to the printed one
--   - generalization: noise ε_k drawn from ε(x_k), a family satisfying (1.7), with (2.5) derived from it → the conditional form (2.5) assumed directly: g_k is 𝒢_{k+1}-measurable, E[ε_k | 𝒢_k] = 0 and E[‖ε_k‖² | 𝒢_k] ≤ δ‖∇f(x_k)‖² + σ² a.s.; reason: every oracle of Definition 1.1 yields (2.5), so the paper's setting is a special case
--   - generalization: initial point x_1 left unspecified → x_1 random, 𝒢_1-strongly measurable with E‖x_1‖² < ∞; y_1 free; z_1 = 0 not assumed; reason: a deterministic x_1 is a special case; y_1 enters only through A_0/A_1 = 0, and (4.6a) at k = 1 forces z_1 = 0
--   - encoding: E‖ε_k‖² used without comment → ‖ε_k‖² integrable, as part of the growth condition; reason: Lean's conditional expectation of a non-integrable function is 0; the condition only excludes cases where the paper's expectations are undefined
--   - encoding: f ∈ F(m, L), m-strongly convex with condition number κ = L/m → 0 < m and m ≤ L as hypotheses; reason: strong convexity and κ = L/m need m > 0; (1.2) forces m ≤ L whenever d ≥ 1, so only the trivial case d = 0 is affected
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, proof of Theorem 5.1, p.24 (display after (5.13))

import Definitions.Def_AccelSGDGrowth_TailDAMSetting
import Definitions.Def_AccelSGDGrowth_tailAverage

open MeasureTheory

namespace AccelSGDGrowth

/-- The first display after (5.13) in the proof of Chen, Na, Kolar, arXiv:2006.06782v4,
Theorem 5.1, p.24: in the setting of Theorem 5.1 (`TailDAMSetting`, `γ₄ = 2L(1+δ)`), with minimizer
`x⋆`, for every `k ≥ 1`,
`E[f(x̄_k) − f(x⋆)] ≤ (1/W_k) Σ_{t=1}^k w_{k,t} E[f(x_t) − f(x⋆)] ≤ (1/(2mW_k)) Σ_{t=1}^k w_{k,t} E‖∇f(x_t)‖²`.

**Formalization Note.** The first step is convexity of `f` along the finite average; the second is
Lemma 2.1(a) at `x⋆`. `W_k > 0` for `k ≥ 1`, and the integrability of every integrand follows from the
setting (milestone "moment bounds"), so the integrals are genuine. -/
theorem jensen_theorem_5_1 {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ mΩ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {m L δ sig2 α : ℝ} (hm : 0 < m) (hmL : m ≤ L) {a η : ℕ → ℝ}
    {x y z g : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
    (hset : TailDAMSetting μ 𝒢 f m L δ sig2 α a η x y z g)
    {xstar : EuclideanSpace ℝ (Fin d)} (hxstar : IsMinOn f Set.univ xstar)
    (k : ℕ) (hk : 1 ≤ k) :
    ∫ ω, (f (tailAverage (2 * L * (1 + δ)) α (fun t => x t ω) k) - f xstar) ∂μ ≤
      1 / totalWeight (2 * L * (1 + δ)) α k *
        ∑ t ∈ Finset.Icc 1 k,
          scheduleW (2 * L * (1 + δ)) α k t * ∫ ω, (f (x t ω) - f xstar) ∂μ ∧
    1 / totalWeight (2 * L * (1 + δ)) α k *
        ∑ t ∈ Finset.Icc 1 k,
          scheduleW (2 * L * (1 + δ)) α k t * ∫ ω, (f (x t ω) - f xstar) ∂μ ≤
      1 / (2 * m * totalWeight (2 * L * (1 + δ)) α k) *
        ∑ t ∈ Finset.Icc 1 k,
          scheduleW (2 * L * (1 + δ)) α k t * ∫ ω, ‖gradient f (x t ω)‖ ^ 2 ∂μ := by sorry

end AccelSGDGrowth
