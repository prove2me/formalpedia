-- Prove2me | Theorems.Thm_BalkemaDeHaan_LimitTypes_lemma_2
-- name    : BalkemaDeHaan.LimitTypes.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:18:34.681986+00:00
-- url     : https://prove2.me/theorems/10ca452b-c27b-4224-9013-cb05dea29c1a
-- title:
--   Lemma 2 — an unbounded non-increasing solution H of (8) agreeing with S where S < 1 agrees with S where H < 1
-- statement:
--   Assume the hypotheses of Lemma 1: $R(x) > 0$ for all $x$, $a(t) > 0$, (2) holds with limit $S$, and $1 - S$ is a nondegenerate distribution function. Let $y$ be a continuity point of $S$ with $0 < S(y) < 1$ and let $(A, B)$, $A \ge 1$, be a pair for $y$ as in Lemma 1, i.e. $S(x)S(y) = S(B + xA)$ whenever $S(x) < 1$.
--
--   Let $x_0 \in [-\infty, \infty)$ and let $H$ be a function on the interval $(x_0, \infty)$, with $y > x_0$, such that
--
--   1. $H$ is non-increasing and unbounded on $(x_0,\infty)$;
--   2. $H(x) = S(x)$ for every $x > x_0$ with $S(x) < 1$;
--   3. $B + xA > x_0$ for every $x > x_0$, and
--   $$H(x)H(y) = H(B + xA) \qquad \text{for } x > x_0. \tag{8}$$
--
--   Then
--   $$H(x) = S(x) \qquad \text{for every } x > x_0 \text{ with } H(x) < 1.$$
--
--   The functional equation (4) alone does not pin down $S$ where $S = 1$; this lemma shows that an explicit solution $H$ of (8) determines $S$ completely, through $S = \min(1, H)$. It is used in both cases of the proof of Theorem 1.
--
--   **Formalization Note** Normalization (2). The left endpoint $x_0$ is an extended real so that $x_0 = -\infty$ (the whole line, used in Case 1 of Theorem 1) is allowed. The condition $B + xA > x_0$ for $x > x_0$ only expresses that (8) is evaluated inside the domain of $H$; the paper's (8) presupposes it. A "pair in Lemma 1" is read as a pair $(A, B)$ with $A \ge 1$ satisfying (4) at $y$; the proof of Lemma 1 shows that this pair is unique.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 795 (PDF 4), Lemma 2, (8)

import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife
import Definitions.Def_BalkemaDeHaan_LimitTypes_LimitLaws

open MeasureTheory ProbabilityTheory Filter Topology

namespace BalkemaDeHaan.LimitTypes

/-- Lemma 2, p. 795 (PDF 4), in the convention (2). The interval `(x₀, ∞)` has `x₀ ∈ [-∞, ∞)`
(an `EReal`), so `x₀ = ⊥` is the whole line. `H` is non-increasing and unbounded on the interval,
agrees with `S` where `S < 1`, and satisfies (8) for a pair `(A, B)` of Lemma 1 (i.e. a pair with
`A ≥ 1` satisfying (4) at `y`). The hypothesis `hdom` says that `B + x A` stays in the interval,
which (8) needs to be meaningful for a function defined on `(x₀, ∞)`. Conclusion: `H = S` where
`H < 1`. -/
theorem lemma_2
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hR : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (a b : ℝ → ℝ) (ha : ∀ t : ℝ, 0 < a t)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ∀ c : ℝ, ν ≠ Measure.dirac c)
    (h2 : WeakConv (normedTail μ a b) (tail ν))
    (y : ℝ) (hyc : ContinuousAt (tail ν) y) (hy0 : 0 < tail ν y) (hy1 : tail ν y < 1)
    (A B : ℝ) (hA : 1 ≤ A)
    (h4 : ∀ x : ℝ, tail ν x < 1 → tail ν x * tail ν y = tail ν (B + x * A))
    (x₀ : EReal) (H : ℝ → ℝ)
    (hH_anti : AntitoneOn H {x : ℝ | x₀ < (x : EReal)})
    (hH_unbdd : ¬ BddAbove (H '' {x : ℝ | x₀ < (x : EReal)}))
    (hHS : ∀ x : ℝ, x₀ < (x : EReal) → tail ν x < 1 → H x = tail ν x)
    (hy_dom : x₀ < (y : EReal))
    (hdom : ∀ x : ℝ, x₀ < (x : EReal) → x₀ < ((B + x * A : ℝ) : EReal))
    (h8 : ∀ x : ℝ, x₀ < (x : EReal) → H x * H y = H (B + x * A)) :
    ∀ x : ℝ, x₀ < (x : EReal) → H x < 1 → H x = tail ν x := by sorry

end BalkemaDeHaan.LimitTypes
