-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_euler_maruyama_solution_aestronglyMeasurable
-- name    : AppliedSDE.SarkkaSolin.euler_maruyama_solution_aestronglyMeasurable
-- status  : Open
-- author  : @Himan
-- created : 2026-11-15T22:44:52.884377+00:00
-- url     : https://prove2.me/theorems/3c650379-86e4-4cfb-9eae-ff7c2e725870
-- title:
--   Euler–Maruyama setting: the SDE solution $X_t$ is almost everywhere measurable
-- statement:
--   **Setting.** Let $W$ be a Brownian motion on a probability space $(\Omega,P)$ with a filtration $\mathcal F$ to which $W$ is adapted and whose future increments are independent of the past. Let $b,\sigma:\mathbb R\to\mathbb R$ be globally Lipschitz with a common constant $L$, and let $T>0$. Let $X$ be a process with almost surely continuous paths, with $E[X_t^2]<\infty$ for $t\in[0,T]$, such that $H(\omega,s)=\sigma(X_s(\omega))$ is jointly measurable, progressively measurable and square integrable on $\Omega\times[0,t]$ for every $t>0$, and such that for every $t\in[0,T]$, almost surely, $$X_t = x_0 + \int_0^t b(X_s)\,ds + \int_0^t \sigma(X_s)\,dW_s,$$ where the last term is the platform's $L^2$ Itô integral `stochasticIntegralBrownian`.
--
--   **Claim.** For every $t\in[0,T]$ the random variable $\omega\mapsto X_t(\omega)$ is almost everywhere strongly measurable with respect to $P$.
--
--   **Why it is needed.** The hypotheses give integrability of $X_t^2$ and joint measurability of $\sigma(X)$, and neither implies measurability of $X_t$ itself (for instance when $\sigma$ is constant). Measurability is required before any second-moment expansion of the Euler–Maruyama error can be written.
--
--   **Proof idea.** On the almost sure event where the path is continuous and the integral equation holds at all rational times in $[0,T]$, the process $J=X-x_0-\int_0^\cdot b(X_s)\,ds$ is the continuous extension of $(I_q)_{q\in\mathbb Q}$, and $Y=X-J$ is the unique solution of the pathwise equation $Y_t=x_0+\int_0^t b(Y_s+J_s)\,ds$. Picard iteration expresses $Y_t$, hence $X_t$, as an almost sure limit of measurable functions of the countable family $(I_q)$.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), https://doi.org/10.1017/9781108186735, Chapter 8, Algorithm 8.1 and Section 8.2 (Euler–Maruyama method and its strong convergence). Child lemma of the Prove2Me theorem AppliedSDE.SarkkaSolin.euler_maruyama_grid_l2_local_error.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology BigOperators

theorem AppliedSDE.SarkkaSolin.euler_maruyama_solution_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (T x₀ : ℝ) (hT : 0 < T)
    (b σ : ℝ → ℝ)
    (hLip : ∃ L : ℝ, 0 ≤ L ∧
      (∀ x y : ℝ, |b x - b y| ≤ L * |x - y|) ∧
      (∀ x y : ℝ, |σ x - σ y| ≤ L * |x - y|))
    (X : ℝ → Ω → ℝ)
    (hXcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => X t ω))
    (hXmom : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
      Integrable (fun ω : Ω => (X t ω) ^ 2) P)
    (H : Ω → ℝ → ℝ)
    (hH : ∀ (ω : Ω) (s : ℝ), H ω s = σ (X s ω))
    (hHmeas : Measurable (Function.uncurry H))
    (hHprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHsq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXeq : ∀ t : ℝ, 0 ≤ t → t ≤ T →
      (fun ω : Ω => X t ω) =ᵐ[P] fun ω : Ω =>
        x₀ + (∫ s in (0 : ℝ)..t, b (X s ω)) +
          LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
            W ℱ hW H hHmeas hHprog hHsq t ω) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
      AEStronglyMeasurable (fun ω : Ω => X t ω) P := by
  sorry
