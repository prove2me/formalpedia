-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_euler_maruyama_strong_half_order
-- name    : AppliedSDE.SarkkaSolin.euler_maruyama_strong_half_order
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:50:56.225136+00:00
-- url     : https://prove2.me/theorems/3261cdf6-e9b9-4d64-9632-5fbb342fd2c2
-- title:
--   Euler–Maruyama has strong mean-square order one-half under global Lipschitz coefficients
-- statement:
--   Särkkä and Solin (2019), Algorithm 8.1 and Section 8.2. Let W be scalar Brownian motion on a filtered probability space and X a continuous adapted solution of the scalar Itô SDE dX=b(X)dt+σ(X)dW with deterministic initial value, where b and σ are globally Lipschitz. Let E(n,k) be the Euler–Maruyama approximation on n equal intervals of a fixed positive horizon T, driven by the exact increments of the same W. Assume the necessary measurability, progressive measurability, stochastic square-energy and finite second-moment conditions for X. The theorem asserts that a constant independent of n bounds the final-time mean-square error by C T/n, which is strong order one-half in root mean square. This is the standard Euler–Maruyama target, and is distinct from the previously existing public Open tamed-Euler theorem.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \mathbb E\left[|X_T-X_T^{(n)}|^2\right]\leq C\,T/n
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Section 8.2, Algorithm 8.1, Equations (8.28)–(8.30), printed pp. 132–133. https://doi.org/10.1017/9781108186735

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology BigOperators

theorem AppliedSDE.SarkkaSolin.euler_maruyama_strong_half_order
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
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 0 < n →
      (∫ ω, (X T ω - E n (Fin.last n) ω) ^ 2 ∂P) ≤
        C * (T / n) := by
  sorry
