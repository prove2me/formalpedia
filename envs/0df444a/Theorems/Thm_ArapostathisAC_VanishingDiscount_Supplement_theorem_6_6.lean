-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_theorem_6_6
-- name    : ArapostathisAC.VanishingDiscount.Supplement.theorem_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:15:07.623803+00:00
-- url     : https://prove2.me/theorems/3db482c7-4ba6-4579-8204-5aa20feda10c
-- title:
--   Theorem 6.6 — under Assumptions 6.8 and 6.11, or 6.9–6.11, a bounded-below solution of the ACOI exists, minimizing selectors are average optimal and $\rho^*$ is the minimum average cost
-- statement:
--   Let $(S,A,U,P,c)$ be a controlled Markov process on Borel spaces with $c\ge0$ possibly unbounded, under the standing Assumptions 2.2 ($P(\cdot\mid x,a)$ weakly continuous on $K$) and 2.3 ($U$ upper semicontinuous, $c$ lower semicontinuous and bounded below on $K$). Suppose either
--
--   1. Assumption 6.8 (for a fixed $x_0$, $h_\beta=J^*_\beta-J^*_\beta(x_0)$ satisfies $-M\le h_{\beta_n}\le b$ along $\beta_n\uparrow1$, with $\int b\,dP(\cdot\mid x,a)<\infty$) and Assumption 6.11 ($P(\cdot\mid x,a)$ strongly continuous in $a$), or
--   2. Assumptions 6.9 ($J(\hat x,\pi)<\infty$ for some $\pi,\hat x$), 6.10 ($\sup_{\beta\in(\beta',1)}\underline h_\beta(x)<\infty$, $\underline h_\beta=J^*_\beta-\inf J^*_\beta$) and 6.11.
--
--   Then there are a constant $\rho^*$ and a measurable function $h$, bounded below, satisfying the ACOI
--   $$\rho^*+h(x)\ge\min_{a\in U(x)}\Big\{c(x,a)+\int_Sh(y)\,P(dy\mid x,a)\Big\},\qquad x\in S,\tag{6.12}$$
--   with the minimum attained; every $\pi\in\Pi_{SD}$ realizing the minimum on the right-hand side of (6.12) is average optimal; and $\rho^*=J^*(x)$ is the minimum average cost at every $x$.
--
--   **Formalization Note** $h_\beta$ and $\underline h_\beta$ are differences of values in $[0,\infty]$ computed in $\mathrm{EReal}$; the bounds of Assumption 6.8 force the finiteness its $h_\beta$ presupposes. $\int h\,dP$ is in $(-\infty,\infty]$ because $h$ is bounded below.
--
--   Differences from the source:
--   - reading: S and A are Borel spaces (Borel subsets of Polish spaces) → separable metrizable topologies whose Borel σ-algebras are standard Borel; reason: a separable metrizable space is homeomorphic to a Borel subset of a Polish space exactly when its Borel σ-algebra is standard; no instance is added or lost
--   - reading: the standing Assumptions 2.1–2.3 (p. 288, assumed throughout unless otherwise indicated); §6.2 drops only the boundedness of c → Assumptions 2.2 and 2.3 are hypotheses; Assumption 2.1 is part of the model; reason: the theorem inherits the paper's standing assumptions (trap 19); Assumption 2.3 also makes the minimum in (6.12) exist
--   - reading: h_β in Assumption 6.8 → h_β(x) = J*_β(x) − J*_β(x₀) for a reference state x₀ chosen in the assumption; reason: p. 322 defines h_β := J*_β(·) − J*_β(x₀) with x₀ ∈ S fixed
--   - reading: β_n ↑ 1 → β_n ∈ (0, 1) nondecreasing with β_n → 1; reason: the usual meaning of the arrow
--   - reading: P(· | x, a) strongly continuous in a (Assumption 6.11) → a ↦ ∫ u dP(· | x, a) continuous on U(x) for every bounded measurable u; reason: P is defined on K, so continuity in a is on U(x)
--   - reading: a function h bounded below satisfying (6.12) with 'min' → h measurable and bounded below, the minimum in (6.12) attained at every x; reason: h ∈ 𝓜(S) as in §6, and the printed 'min'
--   - encoding: J*_β, h_β, h̲_β, J and J* as real or extended-real numbers → values in [0, ∞] (lintegrals of the nonnegative cost), compared in EReal where signed terms occur; reason: Lean convention; costs are nonnegative on K (Assumption 2.1), so the instances are the same and infinite values are represented exactly
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 323, Theorem 6.6, Assumptions 6.8–6.11 and (6.12); p. 322, h_β with fixed x₀; p. 288, Assumption 2.3

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalTriplet_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_BorelCriteria
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_BorelOptimality

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal
open ArapostathisAC.CanonicalTriplet

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Theorem 6.6 (p. 323), on Borel spaces with possibly unbounded costs and the standing
Assumptions 2.2 and 2.3 (p. 288, assumed throughout the paper). Under Assumptions 6.8 and 6.11, or under Assumptions 6.9–6.11, there exist a
constant `ρ*` and a measurable function `h`, bounded below, satisfying the ACOI (6.12) with its
minimum attained; every `f ∈ Π_SD` realizing the minimum on the right-hand side of (6.12) is
average optimal, and `ρ* = J*(x)` is the minimum average cost at every `x`. -/
theorem theorem_6_6 {S A : Type*} [TopologicalSpace S] [MetrizableSpace S]
    [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S] [StandardBorelSpace S]
    [TopologicalSpace A] [MetrizableSpace A] [SecondCountableTopology A] [MeasurableSpace A]
    [BorelSpace A] [StandardBorelSpace A]
    (M : BorelCMP S A) (h22 : Assumption22 M) (h23 : Assumption23 M)
    (hA : (Assumption68 M ∧ Assumption611 M) ∨
      (Assumption69 M ∧ Assumption610 M ∧ Assumption611 M)) :
    ∃ ρs : ℝ, ∃ h : S → ℝ, Measurable h ∧ BddBelow (Set.range h) ∧ ACOI M ρs h ∧
      (∀ f : StationaryPolicy M, RealizesACOIMin M h f → IsAvgOptimal M f) ∧
      ∀ x, (optAvg M x : EReal) = (ρs : EReal) := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
