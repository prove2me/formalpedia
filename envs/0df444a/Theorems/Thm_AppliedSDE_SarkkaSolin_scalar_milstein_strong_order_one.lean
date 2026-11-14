-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_scalar_milstein_strong_order_one
-- name    : AppliedSDE.SarkkaSolin.scalar_milstein_strong_order_one
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:54:12.486974+00:00
-- url     : https://prove2.me/theorems/d92cdbf5-d707-49f5-8e22-c7af8c8e83cb
-- title:
--   Scalar Milstein scheme achieves strong mean-square order one
-- statement:
--   Original derived strong-convergence target from Särkkä and Solin (2019), Algorithm 8.3 and its scalar Milstein update (8.39). Assume global Lipschitz drift and dispersion, C³ regularity and Lipschitz sigma times sigma prime. For an Itô SDE driven by scalar Brownian motion, compare the exact solution with the Milstein iterates driven by the same Brownian increments. The step adds (sigma sigma'/2)(Delta W²-Delta t) to the Euler–Maruyama step. Prove mean-square terminal error at most C (T/n)² with C uniform in n. This is strong order one in root-mean-square error, separate from the existing Euler strong-order-one-half milestone.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \mathbb E[|X_T-X_T^{\mathrm{Milstein},n}|^2]\leq C(T/n)^2
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Section 8.3, Algorithm 8.3, equation (8.39), printed p. 134. https://doi.org/10.1017/9781108186735

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology BigOperators

theorem AppliedSDE.SarkkaSolin.scalar_milstein_strong_order_one
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
    (hSmooth : ContDiff ℝ 3 b ∧ ContDiff ℝ 3 σ)
    (hDiffLip : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ,
      |deriv σ x * σ x - deriv σ y * σ y| ≤ L * |x - y|)
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
            W.W (((k.val : ℝ) * T / n)) ω) +
          (1 / 2 : ℝ) * (deriv σ (E n k.castSucc ω)) *
            σ (E n k.castSucc ω) *
            ((W.W ((((k.val + 1 : ℕ) : ℝ) * T / n)) ω -
              W.W (((k.val : ℝ) * T / n)) ω) ^ 2 - T / n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 0 < n →
      (∫ ω, (X T ω - E n (Fin.last n) ω) ^ 2 ∂P) ≤
        C * (T / n) ^ 2 := by
  sorry
