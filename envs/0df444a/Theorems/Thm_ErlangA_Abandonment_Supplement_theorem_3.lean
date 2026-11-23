-- Prove2me | Theorems.Thm_ErlangA_Abandonment_Supplement_theorem_3
-- name    : ErlangA.Abandonment.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:52:57.509044+00:00
-- url     : https://prove2.me/theorems/de6223c9-08dd-4a73-b710-b358fcc0349c
-- title:
--   Theorem 3 — process and stationary virtual-wait limits, with the exact stationary distribution
-- statement:
--   Let $N\to\infty$ index an unlimited FCFS Erlang-A queue with $N$ agents, arrival rate $\lambda_N>0$, fixed service rate $\mu>0$, and patience rate $\theta_N>0$. Assume $\theta_N\to\theta\in(0,\infty)$ and
--
--   $$\sqrt N\left(1-\frac{\lambda_N}{N\mu}\right)\longrightarrow\beta\in\mathbb R.$$
--
--   The centered count $q_N(0)=(Q_N(0)-N)/\sqrt N$ converges weakly to an arbitrary probability law $\nu$. The queue has the source's mutually independent Poisson arrivals and exponential service and patience primitives. Its marked FCFS realization defines $\upsilon_N(t)$ as the time to service of an infinitely patient hypothetical caller joining at $t$; the entire process uses the same customer histories. There is no initial moment or stationary-start assumption.
--
--   There exists the diffusion $q$ of Theorem 2 with initial law $\nu$, drift $f(x)=-\mu(\beta+x)$ for $x\le0$ and $f(x)=-(\mu\beta+\theta x)$ for $x>0$, and noise coefficient $\sqrt{2\mu}$. Set $v(t)=\max(q(t)/\mu,0)$. Then
--
--   $$\sqrt N\,\upsilon_N\ \Rightarrow\ v\quad\text{in }D[0,\infty)\text{ with }J_1,$$
--
--   and $\sqrt N\,\upsilon_N(t)\Rightarrow v(t)$ for every finite $t\ge0$, including zero. For every $N\ge1$, $\upsilon_N(t)$ has an actual weak limit $\upsilon_N(\infty)$ as $t\to\infty$, equal in law to the explicit waiting-kernel mixture against $\pi$. Also $v(t)\Rightarrow v(\infty)$ as $t\to\infty$, whose law is the positive-part image of the published diffusion density. Both candidate limiting laws are probability measures, and separately
--
--   $$\sqrt N\,\upsilon_N(\infty)\Rightarrow v(\infty).$$
--
--   Write $a=w(-\beta,\sqrt{\mu/\theta})$, with $w(x,y)=[1+h(-xy)/(y h(x))]^{-1}$, $h=\phi/(1-\Phi)$ and $\Psi(x,y)=\phi(x)/(1-\Phi(x+y))$. The exact stationary survival is
--
--   $$\mathbb P(v(\infty)>x)=\begin{cases}1,&x<0,\\a,&x=0,\\a\,h(\beta\sqrt{\mu/\theta})/\Psi(\beta\sqrt{\mu/\theta},\sqrt{\mu\theta}\,x),&x>0.\end{cases}$$
--
--   In particular $\mathbb P(v(\infty)=0)=1-a$. This theorem connects the queue diffusion with virtual waiting times in both transient and stationary regimes, retaining the zero-delay atom.
--
--   **Formalization Note** The diffusion exists in the conclusion. Path convergence uses the published coupling characterization for a continuous limiting process. All scalar law limits use bounded continuous tests, without assuming pointwise CDF convergence at zero. The model's residual exponential clocks give arbitrary initial count laws. No Theorem 2* claim for zero or infinite limiting patience rate is used.
--
--   Differences from the source:
--   - encoding: the N-th FCFS Erlang-A queue and its hypothetical infinitely patient caller → the published count process refined by independent exponential customer marks, with an ordered time-zero batch of initial callers and a common FCFS recursion for every time; reason: this specifies the source joint waiting-time law; exponential residuals permit every initial count law, without stationarity or moment restrictions
--   - encoding: N agents and λ_N tending to infinity in the Section 4 setting → positive rates and model hypotheses for N ≥ 1; N = 0 is an unused totalization; λ_N → ∞ is not a separate premise; reason: the finite QED limit with μ > 0 implies λ_N/(Nμ) → 1 and hence λ_N → ∞
--   - reading: √Nυ_N(t) converges in distribution for 0 ≤ t ≤ ∞, with a process convergence assertion opening the proof on p. 225 → J1 process weak convergence in coupling form, explicit finite-time weak convergence including t = 0, separate long-time limits and stationary weak convergence; reason: this retains both the printed statement and the proof-level process assertion; bounded continuous tests avoid an invalid CDF convergence assertion at the atom
--   - encoding: υ_N(∞) and v(∞) as limiting random variables → the explicit stationary waiting kernel mixture and positive-part pushforward of the published limitDensity, with probability and actual long-time convergence proved in the conclusion; reason: laws determine these variables in distribution and no stationary existence or ergodicity is assumed
--   - encoding: the survival display for x = 0 and x > 0 → the same two branches, with survival 1 for x < 0 and mass 1 − w at zero stated explicitly; reason: nonnegativity of v determines the negative branch and the atom; the display is not extended to x ≤ 0
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 217, Theorem 3; p. 225, Appendix C, proof of Theorem 3 (process convergence); p. 222, conditional waiting law

import Mathlib
import Definitions.Def_ErlangA_Abandonment_Supplement_Customers
import Definitions.Def_ErlangA_Abandonment_Supplement_WaitingLaws
import Definitions.Def_ErlangA_Abandonment_Supplement_psi
import Definitions.Def_ErlangA_Diffusion_SDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace ErlangA.Abandonment.Supplement

open ErlangA.Diffusion BellWilliams2001.ThresholdPolicy DimCallCenters.Rationalized

/-- Theorem 3, p.217, including the process assertion at the opening of its proof, p.225.
All finite times, the actual long-time limits and the separate stationary weak convergence
are retained. The candidate stationary laws are constructed, not arbitrary invariant laws.
The marked FCFS realization retains the queue-induced joint laws of virtual waits. -/
theorem theorem_3 (μ β θ : ℝ) (hμ : 0 < μ) (hθ : 0 < θ)
    (lam thetaN : ℕ → ℝ) (hlam : ∀ N : ℕ, 1 ≤ N → 0 < lam N)
    (hthetaN : ∀ N : ℕ, 1 ≤ N → 0 < thetaN N)
    (hβ : Tendsto (fun N : ℕ => Real.sqrt N * (1 - trafficIntensity lam μ N)) atTop (𝓝 β))
    (hθN : Tendsto thetaN atTop (𝓝 θ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A S R : ℕ → Ω → ℝ → ℝ) (Q : ℕ → Ω → ℝ → ℕ)
    (e s p : ℕ → ℕ → Ω → ℝ)
    (hsys : ∀ N : ℕ, 1 ≤ N →
      IsErlangASystem P N (lam N) μ (thetaN N) (A N) (S N) (R N) (Q N))
    (hfcfs : ∀ N : ℕ, 1 ≤ N →
      IsFCFSRealization P N (lam N) μ (thetaN N) (A N) (Q N) (e N) (s N) (p N))
    (ν : ProbabilityMeasure ℝ)
    (h0 : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun N : ℕ => ∫ ω, g (scaled N (Q N) ω 0 0) ∂P) atTop
      (𝓝 (∫ x, g x ∂(ν : Measure ℝ)))) :
    (∀ N : ℕ, 1 ≤ N → IsProbabilityMeasure (stationaryWaitLaw N (lam N) μ (thetaN N))) ∧
    IsProbabilityMeasure (limitWaitLaw β μ θ) ∧
    (∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 0 ≤ t →
      AEMeasurable (fun ω => waitProcess N (Q N) (e N) (s N) (p N) ω t) P) ∧
    (∀ N : ℕ, 1 ≤ N →
      WeakLawLimit atTop (fun t : ℝ =>
        P.map (fun ω => waitProcess N (Q N) (e N) (s N) (p N) ω t))
        (stationaryWaitLaw N (lam N) μ (thetaN N))) ∧
    WeakLawLimit atTop
      (fun N : ℕ => (stationaryWaitLaw N (lam N) μ (thetaN N)).map
        (fun x => Real.sqrt N * x)) (limitWaitLaw β μ θ) ∧
    (∀ x : ℝ, (limitWaitLaw β μ θ) (Set.Ioi x) = ENNReal.ofReal
      (if x < 0 then 1 else if x = 0 then ErlangA.Staffing.w (-β) (Real.sqrt (μ / θ)) else
        ErlangA.Staffing.w (-β) (Real.sqrt (μ / θ)) * hazard (β * Real.sqrt (μ / θ)) /
          psi (β * Real.sqrt (μ / θ)) (Real.sqrt (μ * θ) * x))) ∧
    (limitWaitLaw β μ θ) {0} = ENNReal.ofReal (1 - ErlangA.Staffing.w (-β) (Real.sqrt (μ / θ))) ∧
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
        (b : ℝ≥0 → Ω' → ℝ) (q : Ω' → ℝ → ℝ),
      IsDiffusionSolution P' μ β θ (ν : Measure ℝ) b q ∧
      CouplingConverges P P'
        (fun N ω t (_ : Fin 1) => Real.sqrt N * waitProcess N (Q N) (e N) (s N) (p N) ω t)
        (fun ω t (_ : Fin 1) => positiveWait μ (q ω t)) ∧
      (∀ t : ℝ, 0 ≤ t → WeakLawLimit atTop
        (fun N : ℕ => P.map (fun ω =>
          Real.sqrt N * waitProcess N (Q N) (e N) (s N) (p N) ω t))
        (P'.map (fun ω => positiveWait μ (q ω t)))) ∧
      WeakLawLimit atTop (fun t : ℝ => P'.map (fun ω => positiveWait μ (q ω t)))
        (limitWaitLaw β μ θ) := by sorry

end ErlangA.Abandonment.Supplement
