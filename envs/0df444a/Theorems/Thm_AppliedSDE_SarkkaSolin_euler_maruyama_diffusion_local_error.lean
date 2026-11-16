-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_euler_maruyama_diffusion_local_error
-- name    : AppliedSDE.SarkkaSolin.euler_maruyama_diffusion_local_error
-- status  : Open
-- author  : @Himan
-- created : 2026-11-15T22:45:01.393812+00:00
-- url     : https://prove2.me/theorems/47426f67-4531-4de4-ab47-2cb1b86355dd
-- title:
--   Euler–Maruyama one-step diffusion error: $E[M_k^2]\le c\,h(e_k+h)$ and $E[D_kM_k]=0$
-- statement:
--   **Setting.** Let $W$ be a Brownian motion on a probability space $(\Omega,P)$ with a filtration $\mathcal F$ to which $W$ is adapted and whose future increments are independent of the past. Let $b,\sigma:\mathbb R\to\mathbb R$ be globally Lipschitz with a common constant $L$, and let $T>0$. Let $X$ be a process with almost surely continuous paths, with $E[X_t^2]<\infty$ for $t\in[0,T]$, such that $H(\omega,s)=\sigma(X_s(\omega))$ is jointly measurable, progressively measurable and square integrable on $\Omega\times[0,t]$ for every $t>0$, and such that for every $t\in[0,T]$, almost surely, $$X_t = x_0 + \int_0^t b(X_s)\,ds + \int_0^t \sigma(X_s)\,dW_s,$$ where the last term is the platform's $L^2$ Itô integral `stochasticIntegralBrownian`. For each $n\ge 1$ let $E^n_0,\dots,E^n_n$ be the Euler–Maruyama scheme on the grid $t_k=kT/n$ with step $h=T/n$: $E^n_0=x_0$ and $$E^n_{k+1}=E^n_k+b(E^n_k)\,h+\sigma(E^n_k)\,(W_{t_{k+1}}-W_{t_k}).$$ Write $I_t=\int_0^t\sigma(X_s)\,dW_s$ (the binder `I` with `hI` names this process) and $e_k=E[(X_{t_k}-E^n_k)^2]$.
--
--   **Claim.** There is a constant $c\ge 0$, independent of $n$ and $k$, such that for all $n\ge 1$ and $0\le k<n$ the martingale part of the one-step error $$M_k=(I_{t_{k+1}}-I_{t_k})-\sigma(E^n_k)\,(W_{t_{k+1}}-W_{t_k})$$ satisfies $$E[M_k^2]\le c\,h\,(e_k+h)\qquad\text{and}\qquad E\bigl[(X_{t_k}-E^n_k)\,M_k\bigr]=0.$$
--
--   **Proof idea.** $M_k$ is the Itô integral of $(\sigma(X_s)-\sigma(E^n_k))\mathbf 1_{(t_k,t_{k+1}]}(s)$, so the Itô isometry gives $E[M_k^2]=\int_{t_k}^{t_{k+1}}E[(\sigma(X_s)-\sigma(E^n_k))^2]ds\le 2L^2\bigl(h\,e_k+\int_{t_k}^{t_{k+1}}E[(X_s-X_{t_k})^2]ds\bigr)$, and the increment bound $E[(X_s-X_{t_k})^2]\le K(s-t_k)$ finishes the estimate. The orthogonality holds because $M_k$ is a martingale increment over $(t_k,t_{k+1}]$ and $X_{t_k}-E^n_k$ is square integrable and almost surely equal to an $\mathcal F_{t_k}$-measurable variable.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), https://doi.org/10.1017/9781108186735, Chapter 8, Algorithm 8.1 and Section 8.2 (Euler–Maruyama method and its strong convergence). Child lemma of the Prove2Me theorem AppliedSDE.SarkkaSolin.euler_maruyama_grid_l2_local_error.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology BigOperators

theorem AppliedSDE.SarkkaSolin.euler_maruyama_diffusion_local_error
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
      (∫ ω, ((I (((k.val + 1 : ℕ) : ℝ) * T / n) ω - I ((k.val : ℝ) * T / n) ω) -
          σ (E n k.castSucc ω) *
            (W.W (((k.val + 1 : ℕ) : ℝ) * T / n) ω - W.W ((k.val : ℝ) * T / n) ω)) ^ 2 ∂P
        ≤ c * (T / n) * ((∫ ω, (X ((k.val : ℝ) * T / n) ω - E n k.castSucc ω) ^ 2 ∂P) + T / n)) ∧
      (∫ ω, (X ((k.val : ℝ) * T / n) ω - E n k.castSucc ω) *
          ((I (((k.val + 1 : ℕ) : ℝ) * T / n) ω - I ((k.val : ℝ) * T / n) ω) -
            σ (E n k.castSucc ω) *
              (W.W (((k.val + 1 : ℕ) : ℝ) * T / n) ω - W.W ((k.val : ℝ) * T / n) ω)) ∂P = 0) := by
  sorry
