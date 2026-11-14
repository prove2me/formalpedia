-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_euler_maruyama_grid_l2_local_error
-- name    : AppliedSDE.SarkkaSolin.euler_maruyama_grid_l2_local_error
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T00:23:42.776727+00:00
-- url     : https://prove2.me/theorems/f933f000-ae1e-4550-8018-ba0ad0177bd4
-- title:
--   Euler-Maruyama uniform grid mean-square local-error recurrence
-- statement:
--   Under the full global Lipschitz Brownian SDE and Euler-Maruyama setup of Applied SDE Chapter 8, establish a constant c independent of the grid size n and actual grid mean-square errors e(k)=E[(X(kT/n)-E_n(k))²], with e(0)<=0 and the true recurrence e(k+1)<=(1+cT/n)e(k)+c(T/n)². This is the substantive stochastic one-step L² estimate needed to prove the Chapter 8 terminal strong-order-half result. The deterministic discrete Gronwall and uniform exponential steps have already been formally proved separately. No a priori terminal-rate assumption or restatement of the parent conclusion is included.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations, Chapter 8, Lipschitz SDE Euler-Maruyama L2 local error estimate.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology BigOperators

theorem AppliedSDE.SarkkaSolin.euler_maruyama_grid_l2_local_error
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
    (E : (n : ℕ) → Fin (n + 1) → Ω → ℝ)
    (hE0 : ∀ (n : ℕ) (ω : Ω), E n 0 ω = x₀)
    (hErec : ∀ (n : ℕ), 0 < n →
      ∀ (k : Fin n) (ω : Ω),
        E n k.succ ω = E n k.castSucc ω +
          b (E n k.castSucc ω) * (T / n) +
          σ (E n k.castSucc ω) *
          (W.W ((((k.val + 1 : ℕ) : ℝ) * T / n)) ω -
            W.W (((k.val : ℝ) * T / n)) ω)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (n : ℕ), 0 < n →
      ∃ e : ℕ → ℝ,
        e 0 ≤ 0 ∧
          (∀ k : ℕ,
            e (k + 1) ≤ (1 + c * (T / n)) * e k + c * (T / n) ^ 2) ∧
          (∀ k : Fin (n + 1),
            e k.val = ∫ ω, (X ((k.val : ℝ) * T / n) ω - E n k ω) ^ 2 ∂P) := by
  sorry
