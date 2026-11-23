-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_theorem_2_1
-- name    : ArapostathisAC.VanishingDiscount.Supplement.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:04:34.216304+00:00
-- url     : https://prove2.me/theorems/81eaeb08-4d51-41d9-8373-e240a3c75457
-- title:
--   Theorem 2.1 — on Borel spaces under Assumptions 2.1–2.3: the DCOE, optimal selectors, existence, value iteration, and lower semicontinuity of $J^*_\beta$
-- statement:
--   Let $(S,A,U,P,c)$ be a controlled Markov process on Borel spaces: $U$ strict, compact-valued with measurable graph $K$, $P$ a stochastic kernel on $S$ given $K$, and $c\ge0$ on $K$ (Assumption 2.1). Assume that $P$ is weakly continuous (Assumption 2.2), and that $U$ is upper semicontinuous and $c$ is lower semicontinuous and bounded below on $K$ (Assumption 2.3). Let $0<\beta<1$ and $T_\beta(v)(x)=\inf_{a\in U(x)}\{c(x,a)+\beta\int v(y)P(dy\mid x,a)\}$. Then:
--
--   1. the discounted cost optimality equation (DCOE) holds:
--   $$J^*_\beta(x)=T_\beta(J^*_\beta)(x)=\inf_{a\in U(x)}\Big\{c(x,a)+\beta\int_SJ^*_\beta(y)\,P(dy\mid x,a)\Big\},\qquad x\in S;$$
--   2. $f\in\Pi_{SD}$ is discount optimal if and only if $f(x)$ attains the infimum in (2.7) for every $x$;
--   3. a discount optimal $f\in\Pi_{SD}$ exists;
--   4. for every bounded lower semicontinuous $g$, $T^k_\beta(g)(x)\to J^*_\beta(x)$ as $k\to\infty$, for every $x$;
--   5. $J^*_\beta$ is nonnegative and lower semicontinuous.
--
--   This is the basic discounted-cost theory on which the vanishing-discount approach to the average cost criterion rests. The published base mission states clauses (i) and (iii) for the countable model; this item is the full theorem on Borel spaces.
--
--   **Formalization Note** $J^*_\beta$ takes values in $[0,\infty]$ (with unbounded costs it may be $+\infty$); $T_\beta$ acts on extended-real functions, with $\int v\,dP=\int v^+dP-\int v^-dP$.
--
--   Differences from the source:
--   - reading: S and A are Borel spaces (Borel subsets of Polish spaces) → separable metrizable topologies whose Borel σ-algebras are standard Borel; reason: a separable metrizable space is homeomorphic to a Borel subset of a Polish space exactly when its Borel σ-algebra is standard; no instance is added or lost
--   - reading: f is discount optimal (ε-optimal for every initial distribution and every ε > 0, p. 287) → J_β(x, f) = J*_β(x) for every x ∈ S; reason: for f ∈ Π_SD the two coincide: J_β(μ, f) = ∫ J_β(x, f) μ(dx) and J_β(μ, π) ≥ ∫ J*_β dμ for every π, while Dirac laws give the converse
--   - encoding: J*_β, T_β and the integrals as real or extended-real numbers → values in [0, ∞] (lintegrals of the nonnegative cost), compared in EReal where signed terms occur; reason: Lean convention; costs are nonnegative on K (Assumption 2.1), so the instances are the same and infinite values are represented exactly
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 289, Theorem 2.1, (2.5)–(2.7); p. 288, Assumptions 2.1–2.3; p. 336, Appendix

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalTriplet_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_BorelCriteria

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal
open ArapostathisAC.CanonicalTriplet

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Theorem 2.1 (p. 289), on Borel state and action spaces. Under Assumptions 2.1–2.3, for every
`β ∈ (0, 1)`:
(i) the DCOE (2.7) `J*_β(x) = T_β(J*_β)(x)` holds for every `x`;
(ii) `f ∈ Π_SD` is discount optimal iff `f(x)` attains the infimum in (2.7) for every `x`;
(iii) a discount optimal `f ∈ Π_SD` exists;
(iv) for every bounded lower semicontinuous `g`, `T_β^k(g)(x) → J*_β(x)` as `k → ∞`;
(v) `J*_β` is nonnegative and lower semicontinuous. -/
theorem theorem_2_1 {S A : Type*} [TopologicalSpace S] [MetrizableSpace S]
    [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S] [StandardBorelSpace S]
    [TopologicalSpace A] [MetrizableSpace A] [SecondCountableTopology A] [MeasurableSpace A]
    [BorelSpace A] [StandardBorelSpace A]
    (M : BorelCMP S A) (h22 : Assumption22 M) (h23 : Assumption23 M)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ x, (discValue M β x : EReal) =
        discBellman M β (fun y => (discValue M β y : EReal)) x) ∧
    (∀ f : StationaryPolicy M, IsDiscOptimal M β f ↔
        ∀ x, (M.c (x, f.1 x) : EReal) +
            (β : EReal) * extIntegral (M.P (x, f.1 x)) (fun y => (discValue M β y : EReal)) =
          discBellman M β (fun y => (discValue M β y : EReal)) x) ∧
    (∃ f : StationaryPolicy M, IsDiscOptimal M β f) ∧
    (∀ g : S → ℝ, LowerSemicontinuous g → (∃ C, ∀ x, |g x| ≤ C) →
      ∀ x, Tendsto (fun k : ℕ => (discBellman M β)^[k] (fun y => (g y : EReal)) x) atTop
        (𝓝 (discValue M β x : EReal))) ∧
    (∀ x, 0 ≤ discValue M β x) ∧ LowerSemicontinuous (discValue M β) := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
