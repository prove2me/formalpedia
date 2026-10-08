-- Prove2me | Theorems.Thm_BalkemaDeHaan_LimitTypes_case_1
-- name    : BalkemaDeHaan.LimitTypes.case_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:18:49.793194+00:00
-- url     : https://prove2.me/theorems/4c94eaa7-2dba-493e-bdfa-4afa3342f9d3
-- title:
--   Proof of Theorem 1, Case 1 — if A(y) = 1 for all y ∈ Y then G is of type Π or Π_γ
-- statement:
--   Assume the hypotheses of Lemma 1: $R(x) > 0$ for all $x$, $a(t) > 0$, the normed conditional tails of (2) converge weakly to $S$, and $G = 1 - S$ is a nondegenerate distribution function. Let $Y$ be the set of continuity points $y$ of $S$ with $S(y) < 1$. Suppose that for every $y \in Y$ the functional equation (4) holds with $A(y) = 1$, i.e. there is $B(y)$ with
--   $$S(x)S(y) = S\big(B(y) + x\big) \qquad \text{whenever } S(x) < 1.$$
--   Then $G$ is of type $\Pi$, or of type $\Pi_\gamma$ for some $\gamma > 0$.
--
--   This is the first of the two cases into which the proof of Theorem 1 splits: a pure shift in (4) yields the exponential law or its discrete analogue.
--
--   **Formalization Note** Normalization (2). Since the pair $(A(y), B(y))$ of Lemma 1 is unique, "$A(y) = 1$" is stated as the existence of a $B(y)$ for which (4) holds with $A = 1$. The paper's auxiliary function $\varphi = \log S$ belongs to the proof and is not part of the statement.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 796 (PDF 5), proof of Theorem 1, Case 1, (9), (10)

import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife
import Definitions.Def_BalkemaDeHaan_LimitTypes_LimitLaws

open MeasureTheory ProbabilityTheory Filter Topology

namespace BalkemaDeHaan.LimitTypes

/-- Proof of Theorem 1, Case 1, p. 796 (PDF 5), in the convention (2): if every continuity point
`y` of `S` with `S(y) < 1` admits (4) with `A(y) = 1`, then `G = 1 - S` is of type `Π` or of
type `Π_γ` for some `γ > 0`. -/
theorem case_1
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hR : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (a b : ℝ → ℝ) (ha : ∀ t : ℝ, 0 < a t)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ∀ c : ℝ, ν ≠ Measure.dirac c)
    (h2 : WeakConv (normedTail μ a b) (tail ν))
    (hA1 : ∀ y : ℝ, ContinuousAt (tail ν) y → tail ν y < 1 →
      ∃ B : ℝ, ∀ x : ℝ, tail ν x < 1 → tail ν x * tail ν y = tail ν (B + x)) :
    IsOfType (cdf ν) PiLaw ∨ ∃ γ : ℝ, 0 < γ ∧ IsOfType (cdf ν) (PiDiscreteLaw γ) := by sorry

end BalkemaDeHaan.LimitTypes
