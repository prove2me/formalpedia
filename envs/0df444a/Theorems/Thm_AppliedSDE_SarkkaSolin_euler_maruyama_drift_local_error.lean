-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_euler_maruyama_drift_local_error
-- name    : AppliedSDE.SarkkaSolin.euler_maruyama_drift_local_error
-- status  : Open
-- author  : @Himan
-- created : 2026-11-15T22:45:10.756808+00:00
-- url     : https://prove2.me/theorems/ab8780b2-5825-4a3d-87c0-7f61da572d52
-- title:
--   Euler–Maruyama one-step drift error: $E[A_k^2]\le c\,h^2(e_k+h)$
-- statement:
--   **Setting.** Let $W$ be a Brownian motion on a probability space $(\Omega,P)$ with a filtration $\mathcal F$ to which $W$ is adapted and whose future increments are independent of the past. Let $b,\sigma:\mathbb R\to\mathbb R$ be globally Lipschitz with a common constant $L$, and let $T>0$. Let $X$ be a process with almost surely continuous paths, with $E[X_t^2]<\infty$ for $t\in[0,T]$, such that $H(\omega,s)=\sigma(X_s(\omega))$ is jointly measurable, progressively measurable and square integrable on $\Omega\times[0,t]$ for every $t>0$, and such that for every $t\in[0,T]$, almost surely, $$X_t = x_0 + \int_0^t b(X_s)\,ds + \int_0^t \sigma(X_s)\,dW_s,$$ where the last term is the platform's $L^2$ Itô integral `stochasticIntegralBrownian`. For each $n\ge 1$ let $E^n_0,\dots,E^n_n$ be the Euler–Maruyama scheme on the grid $t_k=kT/n$ with step $h=T/n$: $E^n_0=x_0$ and $$E^n_{k+1}=E^n_k+b(E^n_k)\,h+\sigma(E^n_k)\,(W_{t_{k+1}}-W_{t_k}).$$ Write $I_t=\int_0^t\sigma(X_s)\,dW_s$ (the binder `I` with `hI` names this process) and $e_k=E[(X_{t_k}-E^n_k)^2]$.
--
--   **Claim.** There is a constant $c\ge 0$, independent of $n$ and $k$, such that for all $n\ge 1$ and $0\le k<n$ the drift part of the one-step error $$A_k=(X_{t_{k+1}}-X_{t_k})-(I_{t_{k+1}}-I_{t_k})-b(E^n_k)\,h$$ satisfies $$E[A_k^2]\le c\,h^2\,(e_k+h).$$
--
--   **Proof idea.** Almost surely $A_k=\int_{t_k}^{t_{k+1}}\bigl(b(X_s)-b(E^n_k)\bigr)ds$. The Lipschitz bound and Cauchy–Schwarz give $A_k^2\le 2L^2\bigl[(\int_{t_k}^{t_{k+1}}|X_s-X_{t_k}|ds)^2+h^2(X_{t_k}-E^n_k)^2\bigr]$. The solution has $\sup_{t\le T}E[X_t^2]<\infty$ and $E[(X_s-X_r)^2]\le K|s-r|$ on $[0,T]$ (Itô isometry, linear growth and Grönwall), which bounds the first term by a multiple of $h^3$.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), https://doi.org/10.1017/9781108186735, Chapter 8, Algorithm 8.1 and Section 8.2 (Euler–Maruyama method and its strong convergence). Child lemma of the Prove2Me theorem AppliedSDE.SarkkaSolin.euler_maruyama_grid_l2_local_error.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology BigOperators

theorem AppliedSDE.SarkkaSolin.euler_maruyama_drift_local_error
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
            W ℱ hW H hHmeas hHprog hHsq t ω)
    (I : ℝ → Ω → ℝ)
    (hI : ∀ (t : ℝ) (ω : Ω), I t ω =
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
        W ℱ hW H hHmeas hHprog hHsq t ω)
    (E : (n : ℕ) → Fin (n + 1) → Ω → ℝ)
    (hE0 : ∀ (n : ℕ) (ω : Ω), E n 0 ω = x₀)
    (hErec : ∀ (n : ℕ), 0 < n →
      ∀ (k : Fin n) (ω : Ω),
        E n k.succ ω = E n k.castSucc ω +
          b (E n k.castSucc ω) * (T / n) +
          σ (E n k.castSucc ω) *
          (W.W ((((k.val + 1 : ℕ) : ℝ) * T / n)) ω -
            W.W (((k.val : ℝ) * T / n)) ω)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (n : ℕ), 0 < n → ∀ k : Fin n,
      ∫ ω, ((X (((k.val + 1 : ℕ) : ℝ) * T / n) ω - X ((k.val : ℝ) * T / n) ω) -
          (I (((k.val + 1 : ℕ) : ℝ) * T / n) ω - I ((k.val : ℝ) * T / n) ω) -
          b (E n k.castSucc ω) * (T / n)) ^ 2 ∂P
        ≤ c * (T / n) ^ 2 * ((∫ ω, (X ((k.val : ℝ) * T / n) ω - E n k.castSucc ω) ^ 2 ∂P) + T / n) := by
  sorry
