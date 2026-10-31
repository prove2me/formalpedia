-- Prove2me | Theorems.Thm_BroadieKaya_SV_exact_simulation
-- name    : BroadieKaya.SV.exact_simulation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:11:53.054485+00:00
-- url     : https://prove2.me/theorems/f45adbe4-4778-4b77-ab77-9b97b8b70b89
-- title:
--   §3 algorithm — exact joint Heston simulation, unbiased pricing, and RMS cost rate
-- statement:
--   Let $(S,V)$ be a solution of the original Heston SDEs with $\kappa,\theta,\sigma_v>0$, $r\in\mathbb R$, $\rho\in[-1,1]$ and positive starting stock. Fix arbitrary deterministic $0\le u<t$ and put $\Delta=t-u$. The four-step ideal sampler draws terminal variance from the explicit real-degree noncentral chi-square law, draws its integrated variance by the exact Fourier inverse CDF conditional on that same terminal variance, recovers the first Brownian integral by (23), and draws the stock using an independent standard normal.
--
--   The sampler's joint output law equals the conditional joint law of $(S_t,V_t)$ given $(S_u,V_u)$ almost everywhere. For each deterministic starting state $(s,v)$ with $s>0$, $v\ge0$, its input law is a probability measure, its output map is almost everywhere measurable, and
--   $$\mathcal L(\widehat S,\widehat V)=\mathcal L(S_t,V_t).$$
--   For every nonnegative measurable terminal payoff, the expectation under these two constructions agrees in $[0,\infty]$, with no moment assumption.
--
--   Let $R_j$ be independent copies of the explicit sampler input on any probability space, and let $f:\mathbb R^2\to\mathbb R$ be any measurable payoff. Define $g=e^{-r\Delta}f$, let $\mu=\mathcal L(S_t,V_t)$, and set
--   $$P_f=\int g\,d\mu,\qquad \widehat P_N=\frac1N\sum_{j=0}^{N-1}g(\operatorname{sample}(R_j)).$$
--   If $g$ is absolutely integrable under $\mu$, then for every integer $N\ge1$ the estimator is integrable and $E[\widehat P_N]=P_f$. If $g$ has a finite second moment, put $\sigma_f^2=\int(g-P_f)^2\,d\mu$. The squared error is integrable and
--   $$\operatorname{MSE}(\widehat P_N)=\frac{\sigma_f^2}{N},\qquad
--   \operatorname{RMSE}(\widehat P_N)=\frac{\sigma_f}{\sqrt N}.$$
--   For every fixed per-path cost $c>0$ and total budget $s_{\rm budget}=cN$,
--   $$\operatorname{RMSE}(\widehat P_N)=\frac{\sigma_f\sqrt c}{\sqrt{s_{\rm budget}}}
--   =O(s_{\rm budget}^{-1/2}).$$
--   The coefficient depends on the model, payoff and per-path cost, not on $N$ or the budget. No payoff moment hypothesis restricts the exact-law assertion, and the finite second moment is not required for the integrable-payoff unbiasedness assertion. Payoffs may depend on both terminal coordinates, as stated in §8.
--
--   Formalization Note: the theorem concerns ideal inversion and exact probability draws, not the finite-tolerance Newton/trapezoidal implementation. Cost is the equal-per-path statistical convention of §1, not bit complexity. The model is defined by local Itô SDEs independently of the sampler. Correlations $\pm1$, all positive real degrees, and zero variance endpoints are included.
--
--   Differences from the source:
--   - encoding: the risk-neutral square-root SDE and Brownian integrals → a usual filtered probability space and the published local Itô integral relation, with κ, θ, σ positive and all real times 0 ≤ u < t; reason: these are the continuous-time model conventions; no Feller condition or global expected energy bound is added
--   - encoding: transition law conditional on the starting state → almost-everywhere equality of regular conditional measures and exact equality of joint laws for deterministic starts; reason: conditioning on a singleton by division is not used
--   - reading: exact simulation alongside numerical inversion at a finite tolerance → the ideal four-step sampler with exact Fourier inversion and exact random draws; reason: the headline exact-law claim and the approximate numerical implementation are distinct
--   - encoding: unbiasedness and an O(s⁻¹ᐟ²) Monte Carlo rate → integrability for real unbiasedness, a finite second moment for RMS, and the exact coefficient σ_f√c at budgets s=cN; reason: these are the expectation and standard-error conventions stated on pp. 217 and 219, with no uniformity over payoffs or models
-- source:
--   Broadie and Kaya, Exact Simulation of Stochastic Volatility and Other Affine Jump Diffusion Processes, Operations Research 54(2), 217–231 (2006), published version, https://doi.org/10.1287/opre.1050.0247; §3 Exact Simulation Algorithm, p. 219 (PDF 3); §3.3 displays after (23), p. 222 (PDF 6); abstract and §1, p. 217 (PDF 1); standard-error identity, p. 219 (PDF 3); §8 payoff scope, p. 229 (PDF 13)

import Definitions.Def_BroadieKaya_SV_MonteCarlo
import Definitions.Def_BroadieKaya_SV_EndpointBridge

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
noncomputable section

namespace BroadieKaya.SV

theorem exact_simulation {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ mΩ)
    (p : HestonParameters) (hp : p.Valid) (u t : ℝ) (hu : 0 ≤ u) (hut : u < t)
    (W₁ W₂ S V : ℝ → Ω → ℝ) (h : IsHeston p P F W₁ W₂ S V u t)
    (hS : ∀ᵐ ω ∂P, 0 < S u ω) :
    (∀ᵐ ω ∂P, condDistrib (fun ω => (S t ω, V t ω))
      (fun ω => (S u ω, V u ω)) P (S u ω, V u ω) =
        sampleLaw p (t-u) (S u ω) (V u ω)) ∧
    ∀ s v : ℝ, 0 < s → 0 ≤ v →
      (∀ᵐ ω ∂P, S u ω = s ∧ V u ω = v) →
      IsProbabilityMeasure (drawLaw p.cir (t-u) v) ∧
      AEMeasurable (sample p (t-u) s v) (drawLaw p.cir (t-u) v) ∧
      HasLaw (fun ω => (S t ω, V t ω)) (sampleLaw p (t-u) s v) P ∧
      (∀ f : ℝ × ℝ → ℝ≥0∞, Measurable f →
        (∫⁻ d, f (sample p (t-u) s v d) ∂(drawLaw p.cir (t-u) v)) =
        ∫⁻ ω, f (S t ω, V t ω) ∂P) ∧
      (∀ {Ξ : Type*} [MeasurableSpace Ξ] (Q : Measure Ξ) [IsProbabilityMeasure Q]
        (R : ℕ → Ξ → Draw), iIndepFun R Q →
        (∀ j, HasLaw (R j) (drawLaw p.cir (t-u) v) Q) →
        ∀ f : ℝ × ℝ → ℝ, Measurable f →
        let μ := P.map (fun ω => (S t ω, V t ω))
        (Integrable (discounted p (t-u) f) μ → ∀ N : ℕ, 1 ≤ N →
          Integrable (estimate p (t-u) s v f R N) Q ∧
          (∫ ξ, estimate p (t-u) s v f R N ξ ∂Q) = price p (t-u) μ f) ∧
        (MemLp (discounted p (t-u) f) 2 μ →
          (∀ N : ℕ, 1 ≤ N →
            Integrable (fun ξ => (estimate p (t-u) s v f R N ξ - price p (t-u) μ f)^2) Q ∧
            mse Q (estimate p (t-u) s v f R N) (price p (t-u) μ f) =
              payoffVariance p (t-u) μ f / N ∧
            Real.sqrt (mse Q (estimate p (t-u) s v f R N) (price p (t-u) μ f)) =
              Real.sqrt (payoffVariance p (t-u) μ f) / Real.sqrt N) ∧
          (∀ c : ℝ, 0 < c →
            (∀ N : ℕ, 1 ≤ N →
              Real.sqrt (mse Q (estimate p (t-u) s v f R N) (price p (t-u) μ f)) =
                Real.sqrt (payoffVariance p (t-u) μ f) * Real.sqrt c / Real.sqrt (c*N)) ∧
            Asymptotics.IsBigO atTop
              (fun N : ℕ => Real.sqrt (mse Q (estimate p (t-u) s v f R N) (price p (t-u) μ f)))
              (fun N : ℕ => (Real.sqrt (c*N))⁻¹)))) := by sorry

end BroadieKaya.SV
