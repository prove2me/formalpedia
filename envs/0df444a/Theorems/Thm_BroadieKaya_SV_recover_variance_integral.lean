-- Prove2me | Theorems.Thm_BroadieKaya_SV_recover_variance_integral
-- name    : BroadieKaya.SV.recover_variance_integral
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:11:44.421417+00:00
-- url     : https://prove2.me/theorems/3389e681-fe1a-40a7-b163-a7a0e2d7ed53
-- title:
--   §3.3, Eq. (23) — recovery of the variance Brownian integral
-- statement:
--   Let $V$ solve the square-root SDE with positive parameters on $[u,t]$, where $0\le u<t$. If $B$ is a continuous version of the actual local Itô integral $B(z)=\int_u^z\sqrt{V_q}\,dW_q^{(1)}$, then almost surely
--   $$B(t)=\frac{V_t-V_u-\kappa\theta(t-u)+\kappa\int_u^tV_q\,dq}{\sigma_v}.$$
--   This recovers the first Brownian integral from terminal and integrated variance. Formalization Note: the left side is supplied with its independent local Itô construction; it is not defined as the right side. The same identity applies to random initial variance, with no positive-endpoint or Feller restriction.
--
--   Differences from the source:
--   - encoding: the risk-neutral square-root SDE and Brownian integrals → a usual filtered probability space and the published local Itô integral relation, with κ, θ, σ positive and all real times 0 ≤ u < t; reason: these are the continuous-time model conventions; no Feller condition or global expected energy bound is added
-- source:
--   Broadie and Kaya, Exact Simulation of Stochastic Volatility and Other Affine Jump Diffusion Processes, Operations Research 54(2), 217–231 (2006), published version, https://doi.org/10.1287/opre.1050.0247; §3.3, (23), p. 221 (PDF 5), using (7), p. 219 (PDF 3)

import Definitions.Def_BroadieKaya_SV_MonteCarlo
import Definitions.Def_BroadieKaya_SV_EndpointBridge

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
noncomputable section

namespace BroadieKaya.SV

theorem recover_variance_integral {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ mΩ)
    (p : CIRParameters) (hp : p.Valid) (u t : ℝ) (hu : 0 ≤ u) (hut : u < t)
    (W V : ℝ → Ω → ℝ) (h : IsCIR p P F W V u t)
    (B : ℝ → Ω → ℝ)
    (hB : EntropyMFG.Enhanced.HasItoIntegral P F W u t
      (fun z ω => Real.sqrt (V z ω)) B) :
    ∀ᵐ ω ∂P, B t ω =
      (V t ω-V u ω-p.kappa*p.theta*(t-u)+p.kappa*area V u t ω)/p.sigma := by sorry

end BroadieKaya.SV
