-- Prove2me | Theorems.Thm_BroadieKaya_SV_variance_transition
-- name    : BroadieKaya.SV.variance_transition
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:11:52.56703+00:00
-- url     : https://prove2.me/theorems/941c7507-541a-4414-88e1-bea00dd42564
-- title:
--   §3.1, Eqs. (8)–(9) — the variance transition law
-- statement:
--   Let $V$ be the nonnegative square-root SDE solution with positive parameters and let $0\le u<t$. Put $\Delta=t-u$, $d=4\kappa\theta/\sigma^2$,
--   $$c=\frac{\sigma^2(1-e^{-\kappa\Delta})}{4\kappa},\qquad
--   \lambda(v)=\frac{4\kappa e^{-\kappa\Delta}v}{\sigma^2(1-e^{-\kappa\Delta})}.$$
--   The conditional law of $V_t$ given $V_u$ is the law of $c\chi_d^{\prime2}(\lambda(V_u))$ almost everywhere. In particular, if $V_u=v\ge0$ almost surely, then $V_t$ has exactly that law with parameter $v$.
--
--   The real-degree noncentral chi-square law is defined independently as the Poisson–gamma mixture on p. 220. All positive real degrees are included; no integer-degree, $d>1$, positive-starting-variance, or Feller restriction is used. Formalization Note: the equality in (8) is equality of distributions; it is not pathwise equality to an independent draw. The sign is the one printed in (8), not the erroneous adjacent prose on p. 220.
--
--   Differences from the source:
--   - encoding: the risk-neutral square-root SDE and Brownian integrals → a usual filtered probability space and the published local Itô integral relation, with κ, θ, σ positive and all real times 0 ≤ u < t; reason: these are the continuous-time model conventions; no Feller condition or global expected energy bound is added
--   - encoding: V_t equals a scaled noncentral chi-square random variable in (8) → equality of regular conditional laws, with the fixed-initial-state specialization; reason: the source equality is distributional
-- source:
--   Broadie and Kaya, Exact Simulation of Stochastic Volatility and Other Affine Jump Diffusion Processes, Operations Research 54(2), 217–231 (2006), published version, https://doi.org/10.1287/opre.1050.0247; §3.1, (8)–(9), p. 219 (PDF 3); (10) and mixture paragraph, p. 220 (PDF 4)

import Definitions.Def_BroadieKaya_SV_MonteCarlo
import Definitions.Def_BroadieKaya_SV_EndpointBridge

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
noncomputable section

namespace BroadieKaya.SV

theorem variance_transition {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ mΩ)
    (p : CIRParameters) (hp : p.Valid) (u t : ℝ) (hu : 0 ≤ u) (hut : u < t)
    (W V : ℝ → Ω → ℝ) (h : IsCIR p P F W V u t) :
    (∀ᵐ ω ∂P, condDistrib (V t) (V u) P (V u ω) = varianceLaw p (t-u) (V u ω)) ∧
    (∀ v : ℝ, 0 ≤ v → (∀ᵐ ω ∂P, V u ω = v) →
      HasLaw (V t) (varianceLaw p (t-u) v) P) := by sorry

end BroadieKaya.SV
