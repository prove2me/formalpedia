-- Prove2me | Theorems.Thm_ChenFarias_SimplePolicy_Supplement_theorem_2
-- name    : ChenFarias.SimplePolicy.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:01:31.237799+00:00
-- url     : https://prove2.me/theorems/b9b33024-615c-4ce1-99e8-de988c918d57
-- title:
--   Theorem 2 (corrected: feedback indices) — HJB verification for regular robust pricing
-- statement:
--   Fix arrival rate $\lambda>0$, horizon $T>0$, inventory $x_0\in\mathbb N$, monitoring-cost lower bound $\underline\theta\ge0$, valuation density $f$, and a bound $B\ge0$ fixed by the problem data. Let $J\in\mathcal J$ solve (11), let $a\in\Pi^M$ attain its supremum at every state, and let $\pi^*$ be any pricing policy built from $J,a$ by (12)–(13). Let $\pi$ be any regular robust pricing policy with the same $B$ and $\underline\theta$, possibly on a different probability space. Then
--   $$
--   \mathbb E\!\left[\int_0^T\lambda\pi_s\bar F(\pi_s)\,ds\right]
--   \le
--   \mathbb E\!\left[\int_0^T\lambda\pi^*_s\bar F(\pi^*_s)\,ds\right],
--   $$
--   where either integrand is zero after its own stockout.
--
--   This is a verification theorem over all the specified solutions and realizations, not an existence assertion for HJB solutions, initial maximizers or feedback trajectories. It compares the full expected-revenue objectives. It imposes neither Assumption 1 nor strict positivity of the density, and does not assume the feedback policy is robust.
--
--   **Formalization Note** The class $\mathcal J$ uses joint differentiability, without $C^1$ regularity. The ordinary drift integral in (12) is required to exist along the realization. The source's measurable-process convention is explicit; the natural pre-time history is used. The Proposition 1 counterexample is not assumed away: Theorem 2 retains every regular robust competitor, including policies with arbitrary unused terminal jump coefficients. A proof must handle that terminal state directly.
--
--   Differences from the source:
--   - correction: pi^{*,M}(s) and sum indexed t_n<s in (12) → a(y_s) for drift and a(y_{t_n}) for jumps with t_n<t; reason: the control has domain Y, and the price at time t includes precisely the earlier sale jumps; §6.2 PDF 15–16 and Appendix B PDF 22 determine these indices
--   - reading: J differentiable in its first two arguments → joint differentiability of (s,p) mapped to J(s,p,x); reason: this is the differentiability needed by the source chain rule; continuous derivatives are not added
--   - encoding: pricing policies with stochastic intensity and conditional expectations → ordered finite event times, their natural histories, and conditional compensator identities on every measurable history event; reason: a finite inventory permits at most x0 unit sales; this is the usual intensity definition and adds no revenue comparison
--   - encoding: ordinary drift integral in (12) → IntegrableOn along almost every realized trajectory; reason: the source integral must exist; this avoids a default zero value for a nonintegrable function and excludes only undefined constructions
--   - encoding: expected nonnegative revenue integral and zero revenue after stockout → iterated lintegral in ENNReal with an explicit inventory indicator; reason: nonnegative prices make ofReal exact; infinity times zero is implemented as zero as in endnote 7
--   - encoding: every regular robust pricing policy → a competitor on any probability space with the same fixed B, including random initial prices; reason: the comparison does not require a coupling, and endnote 12 fixes the control bound by problem data
--   - encoding: left-continuous adapted stochastic processes → jointly measurable versions with path conditions simultaneous almost surely and initial price information in G_0; reason: these are the standard process and initial-history conventions required by the written stochastic integrals
--   - generalization: the standing valuation Assumption 1 of §2 → any nonnegative integrable valuation density supported on [0, infinity) with total mass one; reason: the local drop argument and the HJB verification use the valuation tail as a purchase probability, not monotonicity or a root of the virtual value; specializing to every source valuation law recovers the source domain without adding full support
--   - generalization: the policy defined in (12) is described as regular robust → every IsPricing realization of (12)–(13), with no separate Regular or Restricted premise on the maximizing policy; reason: the comparison needs the maximizing control and its realized feedback equation; every source regular robust realization is included, and no conclusion about selector continuity or realization regularity is assumed
--   - reading: the left derivative in Assumption 2 at the initial endpoint → actual left derivatives for 0<t≤T, with a bounded bookkeeping value d at t=0; condition (10) still includes s=0; reason: the source time interval starts at zero and provides no left neighbourhood there; the counterexample violates (10) also at every interior s<1 on a positive-probability event, independently of this endpoint convention
-- source:
--   Chen and Farias, Robust Dynamic Pricing with Strategic Customers, Mathematics of Operations Research 43(4) (2018), p. 1134, Theorem 2, (11)–(13); p. 1141, proof of Theorem 2

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Supplement_Feedback

namespace ChenFarias.SimplePolicy.Supplement

open MeasureTheory

/-- Theorem 2, with every HJB solution, maximizing feedback, realization and
regular robust competitor, allowing the two policies separate probability spaces. -/
theorem theorem_2
    (lam theta T B : ℝ) (x0 : ℕ) (f : ℝ → ℝ)
    (hlam : 0 < lam) (htheta : 0 ≤ theta) (hT : 0 < T) (hB : 0 ≤ B)
    (hf : IsDensity f) (J : ValueFunction) (hJ : SolvesHJB lam theta T B f J)
    (a : MarkovControl) (ha : MaximizingControl lam theta T B f J a)
    {Ωstar : Type*} [MeasurableSpace Ωstar] (μstar : Measure Ωstar)
    (Pstar : Pricing Ωstar x0) (p0 : ℝ)
    (hPstar : IsPricing Pstar μstar lam T f)
    (hfeedback : IsHJBPolicy Pstar μstar T J a p0)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (P : Pricing Ω x0)
    (hP : IsPricing P μ lam T f)
    (c delta d : ℝ → Ω → ℝ) (hregular : Regular P μ T B c delta d)
    (hrobust : Restricted P μ theta T) :
    expectedRevenue P μ lam T f ≤ expectedRevenue Pstar μstar lam T f := by sorry

end ChenFarias.SimplePolicy.Supplement
