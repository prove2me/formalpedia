-- Prove2me | Theorems.Thm_BroadieKaya_SV_variance_bridge_characteristic
-- name    : BroadieKaya.SV.variance_bridge_characteristic
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:11:40.031873+00:00
-- url     : https://prove2.me/theorems/eee38ece-84cd-4ef9-ad80-e047a57a6484
-- title:
--   §3.2, Eq. (13) — conditional integrated-variance characteristic function
-- statement:
--   For a square-root SDE solution $V$ with positive parameters and $0\le u<t$, put $\Delta=t-u$, $d=4\kappa\theta/\sigma^2$ and $\nu=d/2-1$. For endpoints $v,w\ge0$, write
--   $$q(g)=\frac{4g e^{-g\Delta/2}}{\sigma^2(1-e^{-g\Delta})},$$
--   $$T(g;v,w)=\frac{g e^{-(g-\kappa)\Delta/2}(1-e^{-\kappa\Delta})}{\kappa(1-e^{-g\Delta})}
--   \exp\!\left\{\frac{v+w}{\sigma^2}\left[\frac{\kappa(1+e^{-\kappa\Delta})}{1-e^{-\kappa\Delta}}-\frac{g(1+e^{-g\Delta})}{1-e^{-g\Delta}}\right]\right\}
--   \frac{I_\nu(\sqrt{vw}\,q(g))}{I_\nu(\sqrt{vw}\,q(\kappa))}.$$
--
--   For every real frequency $a$, set $g=\sqrt{\kappa^2-2\sigma^2ia}$ with positive real part. Then the complex exponential is integrable and
--   $$E[e^{ia\int_u^tV_q\,dq}\mid V_u,V_t]=T(g;V_u,V_t)\quad\text{almost surely}.$$
--   For every deterministic starting variance $v\ge0$ and endpoint $w\ge0$, the continuous endpoint bridge exists and its characteristic function is $T(g;v,w)$. The Bessel ratio is continued from frequency zero, including across changes of the principal argument. All real frequencies, including zero, and attainable-zero endpoints are retained. This is the explicit transform inverted by the sampler. Formalization Note: the logarithm of $q(a)/q(0)$ is tracked by integrating $q'/q$ along the real frequency interval; complex analytic continuation is part of the theorem, not an assumed substitution rule.
--
--   Differences from the source:
--   - encoding: the risk-neutral square-root SDE and Brownian integrals → a usual filtered probability space and the published local Itô integral relation, with κ, θ, σ positive and all real times 0 ≤ u < t; reason: these are the continuous-time model conventions; no Feller condition or global expected energy bound is added
--   - encoding: conditioning on endpoint values → regular conditional distributions almost everywhere, and weak limits of positive-width terminal observation windows for fixed initial states; reason: singleton division would not define a bridge; the conclusions certify existence of the endpoint version, including endpoint zero
--   - encoding: the Bessel quotient at nonnegative variance endpoints → the quotient after cancelling the common endpoint power, with its continuous boundary value; reason: this preserves zero endpoints when the two individual Bessel factors vanish or diverge
--   - encoding: continuous branch tracking in (21)–(22) → the logarithm increment ∫₀ᵃ q′(z)/q(z) dz and the entire Bessel factor Hν; reason: the logarithm follows the frequency path without resetting the phase
-- source:
--   Broadie and Kaya, Exact Simulation of Stochastic Volatility and Other Affine Jump Diffusion Processes, Operations Research 54(2), 217–231 (2006), published version, https://doi.org/10.1287/opre.1050.0247; §3.2, (13), p. 220 (PDF 4), with (21)–(22), p. 221 (PDF 5)

import Definitions.Def_BroadieKaya_SV_MonteCarlo
import Definitions.Def_BroadieKaya_SV_EndpointBridge

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
noncomputable section

namespace BroadieKaya.SV

theorem variance_bridge_characteristic {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ mΩ)
    (p : CIRParameters) (hp : p.Valid) (u t : ℝ) (hu : 0 ≤ u) (hut : u < t)
    (W V : ℝ → Ω → ℝ) (h : IsCIR p P F W V u t) :
    (∀ a : ℝ, ∀ᵐ ω ∂P,
      Integrable (fun A : ℝ => Complex.exp (Complex.I*(a : ℂ)*(A : ℂ)))
        (condDistrib (area V u t) (fun ω => (V u ω, V t ω)) P (V u ω, V t ω)) ∧
      (∫ A, Complex.exp (Complex.I*(a : ℂ)*(A : ℂ))
        ∂(condDistrib (area V u t) (fun ω => (V u ω, V t ω)) P (V u ω, V t ω))) =
        bridgeCharacteristic p (t-u) (V u ω) (V t ω) a) ∧
    ∀ v : ℝ, 0 ≤ v → (∀ᵐ ω ∂P, V u ω = v) → ∀ w : ℝ, 0 ≤ w → ∀ a : ℝ,
      HasEndpointBridge P (area V u t) (V t) w (endpointBridge P (area V u t) (V t) w) ∧
      Integrable (fun A : ℝ => Complex.exp (Complex.I*(a : ℂ)*(A : ℂ)))
        (endpointBridge P (area V u t) (V t) w) ∧
      (∫ A, Complex.exp (Complex.I*(a : ℂ)*(A : ℂ))
        ∂(endpointBridge P (area V u t) (V t) w)) =
        bridgeCharacteristic p (t-u) v w a := by sorry

end BroadieKaya.SV
