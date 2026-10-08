-- Prove2me | Theorems.Thm_BalkemaDeHaan_LimitTypes_lemma_1
-- name    : BalkemaDeHaan.LimitTypes.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:17:39.802986+00:00
-- url     : https://prove2.me/theorems/a7c84a4b-5bb4-4fe0-a4ae-e13b42c530ef
-- title:
--   Lemma 1 — the limit tail S satisfies S(x)·S(y) = S(B(y) + xA(y)) with A(y) ≥ 1
-- statement:
--   Let $X$ have distribution tail $R(x) = P\{X > x\} > 0$ for all $x$. Let $a(t) > 0$ and $b(t)$ be functions such that
--   $$P\Big(\frac{X - b(t)}{a(t)} > x \;\Big|\; X > t\Big) \to S(x) \quad \text{weakly as } t \to \infty, \tag{2}$$
--   where $1 - S$ is a nondegenerate distribution function, i.e. $S(x) = \nu((x,\infty))$ for a probability measure $\nu$ on $\mathbb R$ that is not a point mass. Then for each continuity point $y$ of $S$ with $0 < S(y) < 1$ there are constants $A(y) \ge 1$ and $B(y)$ such that
--   $$S(x)\cdot S(y) = S\big(B(y) + x A(y)\big) \qquad \text{for all } x \text{ with } S(x) < 1. \tag{4}$$
--
--   This functional equation is the basis of the classification of the limit laws: Theorem 1 is obtained by solving it.
--
--   **Formalization Note** The statement uses the normalization (2) of §1, which shifts $X$ rather than $X - t$. Weak convergence means convergence at every continuity point of $S$. "Nondegenerate distribution function" is encoded as $S = $ the tail of a probability measure $\nu$ with $\nu \ne \delta_c$ for every $c$; this makes $S$ right-continuous, as the proof uses.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 794 (PDF 3), Lemma 1, (2), (4)

import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife
import Definitions.Def_BalkemaDeHaan_LimitTypes_LimitLaws

open MeasureTheory ProbabilityTheory Filter Topology

namespace BalkemaDeHaan.LimitTypes

/-- Lemma 1, p. 794 (PDF 3), in the convention (2): if the normed tails converge weakly to `S`
and `1 - S` is a nondegenerate distribution function, then for every continuity point `y` of `S`
with `0 < S(y) < 1` there are `A ≥ 1` and `B` with `S(x) S(y) = S(B + x A)` whenever `S(x) < 1`. -/
theorem lemma_1
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hR : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (a b : ℝ → ℝ) (ha : ∀ t : ℝ, 0 < a t)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ∀ c : ℝ, ν ≠ Measure.dirac c)
    (h2 : WeakConv (normedTail μ a b) (tail ν))
    (y : ℝ) (hyc : ContinuousAt (tail ν) y) (hy0 : 0 < tail ν y) (hy1 : tail ν y < 1) :
    ∃ A B : ℝ, 1 ≤ A ∧
      ∀ x : ℝ, tail ν x < 1 → tail ν x * tail ν y = tail ν (B + x * A) := by sorry

end BalkemaDeHaan.LimitTypes
