-- Prove2me | Theorems.Thm_BroadieKaya_SV_bessel_bridge_transform
-- name    : BroadieKaya.SV.bessel_bridge_transform
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:11:23.17971+00:00
-- url     : https://prove2.me/theorems/f188c16e-cb02-471e-9433-4ee832f828af
-- title:
--   Appendix, Eq. (39) — squared Bessel bridge Laplace transform
-- statement:
--   Let $X$ solve $dX_q=n\,dq+2\sqrt{X_q}\,dW_q$, with real dimension $n>0$ and deterministic initial value $X_0=x\ge0$. For every $t>0$, endpoint $y\ge0$ and real $b$, the continuous endpoint bridge law exists. With $\nu=n/2-1$,
--   $$\widetilde E\!\left[e^{-\frac{b^2}{2}\int_0^tX_q\,dq}\mid X_t=y\right]
--   =\frac{bt}{\sinh(bt)}\exp\!\left\{\frac{x+y}{2t}(1-bt\coth(bt))\right\}
--   \frac{I_\nu(\sqrt{xy}\,b/\sinh(bt))}{I_\nu(\sqrt{xy}/t)}.$$
--   The integrand is integrable under that bridge law. At $b=0$ the expression is one. At a zero endpoint the ratio uses its continuous extension, retaining every positive real dimension. This provides the squared Bessel transform used in the Appendix. Formalization Note: the process is defined by its SDE, and the bridge by shrinking endpoint observation windows; neither is defined through this transform.
--
--   Differences from the source:
--   - encoding: squared Bessel process with generator 2xD²+nD → the equivalent SDE dX=n dt+2√X dW on a usual filtered probability space; reason: this specifies the original process without asserting its bridge law
--   - encoding: conditioning on endpoint values → weak limits of positive-width terminal observation windows for the fixed initial state; reason: singleton division would not define a bridge; the conclusions certify existence of the endpoint version, including endpoint zero
--   - encoding: the Bessel quotient at nonnegative variance endpoints → the quotient after cancelling the common endpoint power, with its continuous boundary value; reason: this preserves zero endpoints when the two individual Bessel factors vanish or diverge
--   - encoding: the removable formula at b=0 → the value 1 at b=0; reason: the exponential being averaged is identically one
-- source:
--   Broadie and Kaya, Exact Simulation of Stochastic Volatility and Other Affine Jump Diffusion Processes, Operations Research 54(2), 217–231 (2006), published version, https://doi.org/10.1287/opre.1050.0247; Appendix, (39), p. 229 (PDF 13), with notation on p. 230 (PDF 14)

import Definitions.Def_BroadieKaya_SV_MonteCarlo
import Definitions.Def_BroadieKaya_SV_EndpointBridge

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
noncomputable section

namespace BroadieKaya.SV

theorem bessel_bridge_transform {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ mΩ)
    (n t x y b : ℝ) (hn : 0 < n) (ht : 0 < t) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (W X : ℝ → Ω → ℝ) (h : IsSquaredBessel n P F W X t)
    (hinit : ∀ᵐ ω ∂P, X 0 ω = x) :
    HasEndpointBridge P (area X 0 t) (X t) y
      (endpointBridge P (area X 0 t) (X t) y) ∧
    Integrable (fun A : ℝ => Real.exp (-b^2/2*A))
      (endpointBridge P (area X 0 t) (X t) y) ∧
    (∫ A, Real.exp (-b^2/2*A) ∂(endpointBridge P (area X 0 t) (X t) y)) =
      besselBridgeTransform n t x y b := by sorry

end BroadieKaya.SV
