-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_theorem_6_1
-- name    : ArapostathisAC.VanishingDiscount.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:14:08.510927+00:00
-- url     : https://prove2.me/theorems/a16ff07d-ad94-4c40-86d8-4cf7c6b120a5
-- title:
--   Theorem 6.1 — on Borel spaces, a solution of the ACOE with (6.2) bounds the average cost from below, with equality for minimizing selectors, and gives $J^*\equiv\rho^*$ for a constant $\rho$
-- statement:
--   Let $(S,A,U,P,c)$ be a controlled Markov process on Borel spaces with $c\ge0$, under the standing Assumptions 2.2 ($P(\cdot\mid x,a)$ weakly continuous on $K$) and 2.3 ($U$ upper semicontinuous, $c$ lower semicontinuous and bounded below on $K$), and let $(\rho,h)$ be measurable real functions solving the ACOE
--   $$\rho(x)+h(x)=\inf_{a\in U(x)}\Big\{c(x,a)+\int_Sh(y)\,P(dy\mid x,a)\Big\},\qquad x\in S.\tag{6.1}$$
--   Suppose that for every Markov randomized policy $\pi\in\Pi_M$ and every $x$, $\lim_{t\to\infty}E^\pi_x[h(X_t)/t]=0$ (6.2). Then:
--
--   1. for every $\pi\in\Pi_M$ and $x\in S$,
--   $$\limsup_{n\to\infty}\frac1{n+1}E^\pi_x\Big[\sum_{t=0}^n\rho(X_t)\Big]\le J(x,\pi),\tag{6.3}$$
--   with equality if $\pi\in\Pi_{SD}$ attains the infimum in (6.1) at every $x$;
--   2. if $\rho\equiv\rho^*\in\mathbb R$, then $J^*(x)=\rho^*$ for every $x$, and every $\pi^*\in\Pi_{SD}$ attaining the infimum in (6.1) is average optimal.
--
--   **Formalization Note** $J$ and $J^*$ are in $[0,\infty]$ and $J^*$ is the infimum over all admissible policies. The expectation of $\sum_{t\le n}\rho(X_t)$ is the extended integral $\int(\cdot)^+-\int(\cdot)^-$ in $\mathrm{EReal}$; when $J(x,\pi)<\infty$ its positive part is finite, so it is well defined wherever (6.3) has content.
--
--   Differences from the source:
--   - reading: S and A are Borel spaces (Borel subsets of Polish spaces) → separable metrizable topologies whose Borel σ-algebras are standard Borel; reason: a separable metrizable space is homeomorphic to a Borel subset of a Polish space exactly when its Borel σ-algebra is standard; no instance is added or lost
--   - reading: the standing Assumptions 2.1–2.3 of §2.4 (p. 288: "assumed to hold throughout the paper, unless otherwise indicated"); §6 indicates nothing else for Theorem 6.1 → Assumption 2.2 (weak continuity of P on K) and Assumption 2.3 (U upper semicontinuous; c lower semicontinuous and bounded below on K) are hypotheses; Assumption 2.1 is part of the model; reason: the theorem inherits the paper's standing assumptions (trap 19); stating it without them would be an unverified generalization
--   - reading: the integrals ∫ h(y) P(dy | x, a) in (6.1) → h is P(· | x, a)-integrable for every admissible (x, a), and the infimum is the exact greatest lower bound (IsGLB) of the values over U(x); reason: (6.1) treats these integrals as real numbers; the infimum need not be attained
--   - reading: (6.2) lim_t E^π_x[h(X_t)/t] = 0 → h(X_t) is integrable for every t, and the limit is 0, for every π ∈ Π_M and x; reason: the printed expectations are real numbers
--   - reading: (i) 'There holds (6.3)' → (6.3) for every π ∈ Π_M and every x; reason: the remark after the theorem: '(i), above, says that … for any π ∈ Π_M'
--   - encoding: J(x, π), J*(x) and E[∑ ρ(X_t)] as real or extended-real numbers → values in [0, ∞] (lintegrals of the nonnegative cost), compared in EReal where signed terms occur; reason: Lean convention; costs are nonnegative on K (Assumption 2.1), so the instances are the same and infinite values are represented exactly
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), pp. 315–316, Theorem 6.1, (6.1)–(6.3), and the remark after it

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalTriplet_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_BorelCriteria
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_BorelOptimality

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal
open ArapostathisAC.CanonicalTriplet

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Theorem 6.1 (pp. 315–316), on Borel spaces under the standing Assumptions 2.1–2.3 of §2.4
(p. 288, assumed throughout the paper). Let `(ρ, h)` solve the ACOE (6.1) and suppose that,
for every Markov randomized policy `π ∈ Π_M` and every `x`, `h(X_t)` is integrable and
`E^π_x[h(X_t)/t] → 0` (6.2). Then
(i) for every `π ∈ Π_M` and `x`, `limsup_n (1/(n+1)) E^π_x[∑_{t=0}^n ρ(X_t)] ≤ J(x, π)` (6.3),
with equality when `π = f ∈ Π_SD` attains the infimum in (6.1) at every state;
(ii) if `ρ ≡ ρ*` is constant, then `J*(x) = ρ*` for every `x`, and every `f ∈ Π_SD` attaining the
infimum in (6.1) is average optimal. Expectations of `∑ ρ(X_t)` are extended integrals in
`EReal`. -/
theorem theorem_6_1 {S A : Type*} [TopologicalSpace S] [MetrizableSpace S]
    [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S] [StandardBorelSpace S]
    [TopologicalSpace A] [MetrizableSpace A] [SecondCountableTopology A] [MeasurableSpace A]
    [BorelSpace A] [StandardBorelSpace A]
    (M : BorelCMP S A) (h22 : Assumption22 M) (h23 : Assumption23 M)
    (ρ h : S → ℝ) (hACOE : BorelACOE M ρ h)
    (h62 : ∀ π : MarkovPolicy M, ∀ x : S,
      (∀ t : ℕ, Integrable (fun ω : ℕ → S × A => h (ω t).1) (pathMeasure M π.toPolicy x)) ∧
      Tendsto (fun t : ℕ => ∫ ω, h (ω t).1 / (t : ℝ) ∂(pathMeasure M π.toPolicy x)) atTop
        (𝓝 0)) :
    (∀ π : MarkovPolicy M, ∀ x : S,
      limsup (fun n : ℕ => (((n : ℝ) + 1)⁻¹ : EReal) *
          extIntegral (pathMeasure M π.toPolicy x)
            (fun ω => ((∑ t ∈ Finset.range (n + 1), ρ (ω t).1 : ℝ) : EReal))) atTop ≤
        (avgCost M π.toPolicy x : EReal)) ∧
    (∀ f : StationaryPolicy M, AttainsACOE M ρ h f → ∀ x : S,
      limsup (fun n : ℕ => (((n : ℝ) + 1)⁻¹ : EReal) *
          extIntegral (pathMeasure M f.toPolicy x)
            (fun ω => ((∑ t ∈ Finset.range (n + 1), ρ (ω t).1 : ℝ) : EReal))) atTop =
        (avgCost M f.toPolicy x : EReal)) ∧
    (∀ ρs : ℝ, (∀ x, ρ x = ρs) →
      (∀ x, (optAvg M x : EReal) = (ρs : EReal)) ∧
      ∀ f : StationaryPolicy M, AttainsACOE M ρ h f → IsAvgOptimal M f) := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
