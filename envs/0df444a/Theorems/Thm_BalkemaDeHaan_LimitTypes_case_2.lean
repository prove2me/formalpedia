-- Prove2me | Theorems.Thm_BalkemaDeHaan_LimitTypes_case_2
-- name    : BalkemaDeHaan.LimitTypes.case_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:20:21.750977+00:00
-- url     : https://prove2.me/theorems/05ac1283-621a-4df6-b14b-4ae3df343bfe
-- title:
--   Proof of Theorem 1, Case 2 — if A(y) > 1 for some y ∈ Y then G is of type Γ_α or Γ_{γ,α}
-- statement:
--   Assume the hypotheses of Lemma 1: $R(x) > 0$ for all $x$, $a(t) > 0$, the normed conditional tails of (2) converge weakly to $S$, and $G = 1 - S$ is a nondegenerate distribution function. Suppose there are a continuity point $y$ of $S$ with $S(y) < 1$ and constants $A > 1$ and $B$ with
--   $$S(x)S(y) = S(B + xA) \qquad \text{whenever } S(x) < 1.$$
--   Then $G$ is of type $\Gamma_\alpha$ for some $\alpha > 0$, or of type $\Gamma_{\gamma,\alpha}$ for some $\gamma, \alpha > 0$.
--
--   This is the second case of the proof of Theorem 1: a genuine scale factor in (4) yields the Pareto-type law $\Gamma_\alpha$ or its discrete analogue.
--
--   **Formalization Note** Normalization (2). Since the pair of Lemma 1 is unique, "$A(y) > 1$ for some $y \in Y$" is stated as the existence of such a $y$ and a pair $(A, B)$ with $A > 1$ satisfying (4).
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), pp. 796–797 (PDF 5–6), proof of Theorem 1, Case 2

import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife
import Definitions.Def_BalkemaDeHaan_LimitTypes_LimitLaws

open MeasureTheory ProbabilityTheory Filter Topology

namespace BalkemaDeHaan.LimitTypes

/-- Proof of Theorem 1, Case 2, pp. 796–797 (PDF 5–6), in the convention (2): if some continuity
point `y` of `S` with `S(y) < 1` admits (4) with `A(y) > 1`, then `G = 1 - S` is of type `Γ_α`
for some `α > 0` or of type `Γ_{γ,α}` for some `γ, α > 0`. -/
theorem case_2
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hR : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (a b : ℝ → ℝ) (ha : ∀ t : ℝ, 0 < a t)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ∀ c : ℝ, ν ≠ Measure.dirac c)
    (h2 : WeakConv (normedTail μ a b) (tail ν))
    (hA : ∃ y : ℝ, ContinuousAt (tail ν) y ∧ tail ν y < 1 ∧
      ∃ A B : ℝ, 1 < A ∧ ∀ x : ℝ, tail ν x < 1 → tail ν x * tail ν y = tail ν (B + x * A)) :
    (∃ α : ℝ, 0 < α ∧ IsOfType (cdf ν) (GammaLaw α)) ∨
      ∃ γ : ℝ, 0 < γ ∧ ∃ α : ℝ, 0 < α ∧ IsOfType (cdf ν) (GammaDiscreteLaw γ α) := by sorry

end BalkemaDeHaan.LimitTypes
