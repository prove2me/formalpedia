-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_euler_maruyama_scheme_memLp_two
-- name    : AppliedSDE.SarkkaSolin.euler_maruyama_scheme_memLp_two
-- status  : Proved
-- author  : @Himan
-- created : 2026-11-15T22:44:51.803484+00:00
-- url     : https://prove2.me/theorems/997f27c1-35e9-4445-bbff-48b1c9faec8e
-- title:
--   Euler–Maruyama iterates are square integrable
-- statement:
--   **Setting.** Let $W$ be a Brownian motion on a probability space $(\Omega,P)$ with a filtration $\mathcal F$ to which $W$ is adapted and whose future increments are independent of the past. Let $b,\sigma:\mathbb R\to\mathbb R$ be globally Lipschitz with a common constant $L$, and let $T>0$. For each $n\ge 1$ let $E^n_0,\dots,E^n_n$ be the Euler–Maruyama scheme on the grid $t_k=kT/n$ with step $h=T/n$: $E^n_0=x_0$ and $$E^n_{k+1}=E^n_k+b(E^n_k)\,h+\sigma(E^n_k)\,(W_{t_{k+1}}-W_{t_k}).$$
--
--   **Claim.** For every $n\ge 1$ and every $k\in\{0,\dots,n\}$ the iterate $E^n_k$ belongs to $L^2(P)$.
--
--   **Proof idea.** Induction on $k$. The iterate $E^n_k$ is $\mathcal F_{t_k}$-measurable, the maps $b,\sigma$ have linear growth, and the increment $W_{t_{k+1}}-W_{t_k}$ is Gaussian and independent of $\mathcal F_{t_k}$, so $E[\sigma(E^n_k)^2(W_{t_{k+1}}-W_{t_k})^2]=h\,E[\sigma(E^n_k)^2]<\infty$.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), https://doi.org/10.1017/9781108186735, Chapter 8, Algorithm 8.1 and Section 8.2 (Euler–Maruyama method and its strong convergence). Child lemma of the Prove2Me theorem AppliedSDE.SarkkaSolin.euler_maruyama_grid_l2_local_error.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology BigOperators

theorem AppliedSDE.SarkkaSolin.euler_maruyama_scheme_memLp_two
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
    (E : (n : ℕ) → Fin (n + 1) → Ω → ℝ)
    (hE0 : ∀ (n : ℕ) (ω : Ω), E n 0 ω = x₀)
    (hErec : ∀ (n : ℕ), 0 < n →
      ∀ (k : Fin n) (ω : Ω),
        E n k.succ ω = E n k.castSucc ω +
          b (E n k.castSucc ω) * (T / n) +
          σ (E n k.castSucc ω) *
          (W.W ((((k.val + 1 : ℕ) : ℝ) * T / n)) ω -
            W.W (((k.val : ℝ) * T / n)) ω)) :
    ∀ (n : ℕ), 0 < n → ∀ k : Fin (n + 1), MemLp (E n k) 2 P := by
  sorry
