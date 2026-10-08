-- Prove2me | Theorems.Thm_BalkemaDeHaan_LimitTypes_corollary_lemma_1
-- name    : BalkemaDeHaan.LimitTypes.corollary_lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:17:55.244761+00:00
-- url     : https://prove2.me/theorems/7ed4786d-792d-4658-bfd4-ecba9bc4a704
-- title:
--   Corollary to Lemma 1 — the limit tail S is strictly positive
-- statement:
--   Under the hypotheses of Lemma 1 — $R(x) > 0$ for all $x$, $a(t) > 0$, the normed conditional tails of (2) converging weakly to $S$, and $1 - S$ a nondegenerate distribution function — the limit tail is strictly positive:
--   $$S(x) > 0 \qquad \text{for all } x \in \mathbb R.$$
--
--   So a nondegenerate limit law of the residual life time has unbounded support to the right; it is used to show that $\log S$ is finite where $S < 1$.
--
--   **Formalization Note** Same encoding as Lemma 1: the normalization (2), weak convergence at continuity points of $S$, and $S$ the tail of a probability measure $\nu$ that is not a point mass.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 795 (PDF 4), Corollary (to Lemma 1)

import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife
import Definitions.Def_BalkemaDeHaan_LimitTypes_LimitLaws

open MeasureTheory ProbabilityTheory Filter Topology

namespace BalkemaDeHaan.LimitTypes

/-- Corollary to Lemma 1, p. 795 (PDF 4): under the hypotheses of Lemma 1 the limit tail `S` is
strictly positive everywhere. -/
theorem corollary_lemma_1
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hR : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (a b : ℝ → ℝ) (ha : ∀ t : ℝ, 0 < a t)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ∀ c : ℝ, ν ≠ Measure.dirac c)
    (h2 : WeakConv (normedTail μ a b) (tail ν)) :
    ∀ x : ℝ, 0 < tail ν x := by sorry

end BalkemaDeHaan.LimitTypes
