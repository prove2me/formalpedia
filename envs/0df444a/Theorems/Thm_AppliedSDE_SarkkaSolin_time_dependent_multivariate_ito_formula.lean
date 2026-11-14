-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_time_dependent_multivariate_ito_formula
-- name    : AppliedSDE.SarkkaSolin.time_dependent_multivariate_ito_formula
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:59:16.425656+00:00
-- url     : https://prove2.me/theorems/62f0e638-2c30-410c-89d2-fdf5ec31a390
-- title:
--   Time-dependent multidimensional Itô formula with general finite Brownian drivers
-- statement:
--   Särkkä and Solin (2019), Theorem 4.2, equations (4.14)–(4.15), printed p. 47. For an n-dimensional Itô semimartingale driven by d independent Brownian coordinates, with adapted bounded drift and bounded progressively measurable dispersion, and a scalar test function f(t,x) having a continuous time derivative and bounded first/second spatial derivatives, prove the complete time-dependent multivariate Itô formula. Its drift is ∂_t f+Σ_i∂_i f b_i+(1/2)Σ_{i,j,k}∂_{ij}²f H_{ik}H_{jk}; the stochastic term is Σ_{i,k}∫ ∂_i f(t,X_t)H_{ik}dW^k_t. The required stochastic-integral adaptedness and square energy are explicit. This fills the gap between existing public scalar time-dependent and vector time-independent Itô results. The time derivative and first/second spatial derivatives are jointly continuous in time and state, ensuring the C¹,² regularity required by the source's time-dependent Itô chain rule.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \mathrm df(t,X_t)=\left(\partial_tf+\nabla f\cdot b+\frac12\operatorname{tr}(HH^\top\nabla^2f)\right)\mathrm dt+\nabla f^\top H\,\mathrm dW_t
--   $$
-- source:
--   Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Theorem 4.2 and equations (4.14)–(4.15), printed p. 47. https://doi.org/10.1017/9781108186735

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoFormula
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Ito
open scoped NNReal ENNReal Topology BigOperators
open LevyStochCalc

theorem AppliedSDE.SarkkaSolin.time_dependent_multivariate_ito_formula
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ}
    {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {hcoord : ∀ k : Fin d,
      LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ}
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ}
    {bdrift : Fin n → Ω → ℝ → ℝ}
    {X : ℝ → Ω → Fin n → ℝ}
    {C : ℝ} (hC0 : 0 ≤ C)
    (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ),
      |H p k ω s| ≤ C)
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    (hma : ∀ (p q : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : ∀ (p q : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ (p q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : ℝ → (Fin n → ℝ) → ℝ}
    {ft : ℝ → (Fin n → ℝ) → ℝ}
    {fx : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {fxx : ℝ → (Fin n → ℝ) →
       (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (ht : ∀ s z, HasDerivAt (fun r => f r z) (ft s z) s)
    (hx : ∀ s z, HasFDerivAt (f s) (fx s z) z)
    (hxx : ∀ s z, HasFDerivAt (fx s) (fxx s z) z)
    (hftc : Continuous (Function.uncurry ft))
    (hfxc : Continuous (Function.uncurry fx))
    (hfxxc : Continuous (Function.uncurry fxx))
    (hfxxunif : ∀ (s : ℝ) (ε : ℝ), 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ z w : Fin n → ℝ,
        ‖z - w‖ < δ → ‖fxx s z - fxx s w‖ ≤ ε)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hfbd : ∀ (s : ℝ) (z : Fin n → ℝ),
      |ft s z| ≤ K ∧ ‖fx s z‖ ≤ K ∧ ‖fxx s z‖ ≤ K)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s =>
        coordDeriv (fx s) p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ fun ω s =>
        coordDeriv (fx s) p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv (fx s) p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f T (X T ω) - f 0 (X 0 ω)) =ᵐ[P]
      fun ω : Ω =>
        (∫ s in Set.Ioc (0 : ℝ) T, ft s (X s ω) ∂volume)
          + (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv (fx s) p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d,
              stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
                (fun ω s =>
                  coordDeriv (fx s) p (X s ω) * H p k ω s)
                (hmg p k) (hpg p k) (hqg p k) T ω)
          + (1 / 2 : ℝ) * ∑ p : Fin n, ∑ q : Fin n,
              ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv₂ (fxx s) p q (X s ω) *
                  (∑ k : Fin d, H p k ω s * H q k ω s) ∂volume := by
  sorry
