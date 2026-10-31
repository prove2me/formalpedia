-- Prove2me | Theorems.Thm_BroadieKaya_SV_variance_bridge_laplace
-- name    : BroadieKaya.SV.variance_bridge_laplace
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:11:30.410101+00:00
-- url     : https://prove2.me/theorems/0e6376b1-d73e-4ed4-bb9e-4f6ccf280b98
-- title:
--   Appendix, Eq. (40) — square-root bridge Laplace transform
-- statement:
--   For a square-root SDE solution $V$ with positive parameters and $0\le u<t$, put $\Delta=t-u$, $d=4\kappa\theta/\sigma^2$ and $\nu=d/2-1$. For endpoints $v,w\ge0$, write
--   $$q(g)=\frac{4g e^{-g\Delta/2}}{\sigma^2(1-e^{-g\Delta})},$$
--   $$T(g;v,w)=\frac{g e^{-(g-\kappa)\Delta/2}(1-e^{-\kappa\Delta})}{\kappa(1-e^{-g\Delta})}
--   \exp\!\left\{\frac{v+w}{\sigma^2}\left[\frac{\kappa(1+e^{-\kappa\Delta})}{1-e^{-\kappa\Delta}}-\frac{g(1+e^{-g\Delta})}{1-e^{-g\Delta}}\right]\right\}
--   \frac{I_\nu(\sqrt{vw}\,q(g))}{I_\nu(\sqrt{vw}\,q(\kappa))}.$$
--
--   For every $a\ge0$, set $g=\sqrt{\kappa^2+2\sigma^2a}$. The conditional exponential is integrable and
--   $$E[e^{-a\int_u^tV_q\,dq}\mid V_u,V_t]=T(g;V_u,V_t)\quad\text{almost surely}.$$
--   For each deterministic starting state $v\ge0$ and every endpoint $w\ge0$, the continuous endpoint bridge exists and its integrable Laplace transform equals $T(g;v,w)$. This includes $a=0$ and zero endpoints. It is the variance-domain transform in the Appendix, without assuming the change-of-law identity as a hypothesis. Formalization Note: $\sigma$ means $\sigma_v$, and the ratio is evaluated through the cancelled entire Bessel factor at zero endpoints.
--
--   Differences from the source:
--   - encoding: the risk-neutral square-root SDE and Brownian integrals → a usual filtered probability space and the published local Itô integral relation, with κ, θ, σ positive and all real times 0 ≤ u < t; reason: these are the continuous-time model conventions; no Feller condition or global expected energy bound is added
--   - encoding: conditioning on endpoint values → regular conditional distributions almost everywhere, and weak limits of positive-width terminal observation windows for fixed initial states; reason: singleton division would not define a bridge; the conclusions certify existence of the endpoint version, including endpoint zero
--   - encoding: the Bessel quotient at nonnegative variance endpoints → the quotient after cancelling the common endpoint power, with its continuous boundary value; reason: this preserves zero endpoints when the two individual Bessel factors vanish or diverge
-- source:
--   Broadie and Kaya, Exact Simulation of Stochastic Volatility and Other Affine Jump Diffusion Processes, Operations Research 54(2), 217–231 (2006), published version, https://doi.org/10.1287/opre.1050.0247; Appendix, (40), p. 230 (PDF 14); parameter definitions on p. 229 (PDF 13)

import Definitions.Def_BroadieKaya_SV_MonteCarlo
import Definitions.Def_BroadieKaya_SV_EndpointBridge

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
noncomputable section

namespace BroadieKaya.SV

theorem variance_bridge_laplace {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ mΩ)
    (p : CIRParameters) (hp : p.Valid) (u t : ℝ) (hu : 0 ≤ u) (hut : u < t)
    (W V : ℝ → Ω → ℝ) (h : IsCIR p P F W V u t) :
    (∀ a : ℝ, 0 ≤ a → ∀ᵐ ω ∂P,
      Integrable (fun A : ℝ => Real.exp (-a*A))
        (condDistrib (area V u t) (fun ω => (V u ω, V t ω)) P (V u ω, V t ω)) ∧
      (∫ A, Real.exp (-a*A)
        ∂(condDistrib (area V u t) (fun ω => (V u ω, V t ω)) P (V u ω, V t ω))) =
        bridgeLaplace p (t-u) (V u ω) (V t ω) a) ∧
    ∀ v : ℝ, 0 ≤ v → (∀ᵐ ω ∂P, V u ω = v) → ∀ w : ℝ, 0 ≤ w → ∀ a : ℝ, 0 ≤ a →
      HasEndpointBridge P (area V u t) (V t) w (endpointBridge P (area V u t) (V t) w) ∧
      Integrable (fun A : ℝ => Real.exp (-a*A)) (endpointBridge P (area V u t) (V t) w) ∧
      (∫ A, Real.exp (-a*A) ∂(endpointBridge P (area V u t) (V t) w)) =
        bridgeLaplace p (t-u) v w a := by sorry

end BroadieKaya.SV
