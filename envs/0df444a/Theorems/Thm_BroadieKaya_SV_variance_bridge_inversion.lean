-- Prove2me | Theorems.Thm_BroadieKaya_SV_variance_bridge_inversion
-- name    : BroadieKaya.SV.variance_bridge_inversion
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:11:43.874608+00:00
-- url     : https://prove2.me/theorems/cccc6fbd-aa07-4b27-96b3-0928db4abecc
-- title:
--   §3.2, Eq. (14) — both Fourier inversions of the bridge CDF
-- statement:
--   For a square-root diffusion with positive parameters on $[u,t]$, let $\Phi_{v,w}$ be the explicit continued characteristic expression (13), and let $F_{v,w}$ be the candidate CDF defined by the half-line inversion. For a random starting state, the regular conditional law of $\int_u^tV_q\,dq$ given $(V_u,V_t)$ has CDF $F_{V_u,V_t}$ almost surely, simultaneously for every real $x$.
--
--   For every fixed starting variance $v\ge0$ and endpoint $w\ge0$, the continuous endpoint bridge exists, is atomless, and has the continuous, nondecreasing CDF $F_{v,w}$, with limit one at infinity and value zero for negative $x$. For every $x\ge0$, both limits exist and give
--   $$F_{v,w}(x)=\frac1\pi\lim_{R\to\infty}\int_{-R}^{R}\frac{\sin(ax)}a\Phi_{v,w}(a)\,da
--   =\frac2\pi\lim_{R\to\infty}\int_0^R\frac{\sin(ax)}a\operatorname{Re}\Phi_{v,w}(a)\,da.$$
--   For $0<U<1$, the quantile set $\{x\ge0:U\le F_{v,w}(x)\}$ is nonempty and bounded below. Applying its infimum to a uniform random variable on $(0,1)$ yields exactly the bridge law. These assertions justify the inverse-transform step following (22). Formalization Note: neither CDF validity nor absence of atoms is a premise, and the frequency-zero integrand has the removable value $x$.
--
--   Differences from the source:
--   - encoding: the risk-neutral square-root SDE and Brownian integrals → a usual filtered probability space and the published local Itô integral relation, with κ, θ, σ positive and all real times 0 ≤ u < t; reason: these are the continuous-time model conventions; no Feller condition or global expected energy bound is added
--   - encoding: conditioning on endpoint values → regular conditional distributions almost everywhere, and weak limits of positive-width terminal observation windows for fixed initial states; reason: singleton division would not define a bridge; the conclusions certify existence of the endpoint version, including endpoint zero
--   - encoding: the two infinite Fourier integrals and inverse transform → limits over [−R,R] and [0,R], with CDF validity, atomlessness and inverse-CDF sampling asserted in the conclusion; reason: this makes existence and the source sampling step explicit without assuming the distribution to be proved
-- source:
--   Broadie and Kaya, Exact Simulation of Stochastic Volatility and Other Affine Jump Diffusion Processes, Operations Research 54(2), 217–231 (2006), published version, https://doi.org/10.1287/opre.1050.0247; §3.2, (14), p. 220 (PDF 4); inverse-transform paragraph after (22), p. 221 (PDF 5)

import Definitions.Def_BroadieKaya_SV_MonteCarlo
import Definitions.Def_BroadieKaya_SV_EndpointBridge

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
noncomputable section

namespace BroadieKaya.SV

theorem variance_bridge_inversion {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ mΩ)
    (p : CIRParameters) (hp : p.Valid) (u t : ℝ) (hu : 0 ≤ u) (hut : u < t)
    (W V : ℝ → Ω → ℝ) (h : IsCIR p P F W V u t) :
    (∀ᵐ ω ∂P, ∀ x : ℝ,
      (condDistrib (area V u t) (fun ω => (V u ω, V t ω)) P
        (V u ω, V t ω)) (Iic x) = ENNReal.ofReal (bridgeCDF p (t-u) (V u ω) (V t ω) x)) ∧
    ∀ v : ℝ, 0 ≤ v → (∀ᵐ ω ∂P, V u ω = v) → ∀ w : ℝ, 0 ≤ w →
      HasEndpointBridge P (area V u t) (V t) w (endpointBridge P (area V u t) (V t) w) ∧
      (∀ x : ℝ, (endpointBridge P (area V u t) (V t) w) {x} = 0) ∧
      Continuous (bridgeCDF p (t-u) v w) ∧
      Monotone (bridgeCDF p (t-u) v w) ∧
      Tendsto (bridgeCDF p (t-u) v w) atTop (𝓝 1) ∧
      (∀ x : ℝ, (endpointBridge P (area V u t) (V t) w) (Iic x) =
        ENNReal.ofReal (bridgeCDF p (t-u) v w x)) ∧
      (∀ x : ℝ, 0 ≤ x →
        Tendsto (halfInversion p (t-u) v w x) atTop (𝓝 (bridgeCDF p (t-u) v w x)) ∧
        Tendsto (fullInversion p (t-u) v w x) atTop
          (𝓝 ((bridgeCDF p (t-u) v w x : ℝ) : ℂ))) ∧
      (∀ U : ℝ, 0 < U → U < 1 →
        {x : ℝ | 0 ≤ x ∧ U ≤ bridgeCDF p (t-u) v w x}.Nonempty ∧
        BddBelow {x : ℝ | 0 ≤ x ∧ U ≤ bridgeCDF p (t-u) v w x}) ∧
      HasLaw (bridgeQuantile p (t-u) v w)
        (endpointBridge P (area V u t) (V t) w) (volume.restrict (Ioo (0 : ℝ) 1)) := by sorry

end BroadieKaya.SV
