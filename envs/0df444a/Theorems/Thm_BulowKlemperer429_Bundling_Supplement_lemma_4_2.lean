-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_Supplement_lemma_4_2
-- name    : BulowKlemperer429.Bundling.Supplement.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:38:22.163519+00:00
-- url     : https://prove2.me/theorems/9930cff0-c919-4fbf-bff7-50dd5bae39c8
-- title:
--   Lemma 4.2 — tensorization of cumulative entropy $L$
-- statement:
--   Let $V=(V_1,\dots,V_m)$ have independent coordinates and let $h(V)$ be a bounded nonnegative random variable. For a real random variable $X$ with distribution function $F_X(t)=\Pr[X\le t]$, its cumulative entropy is
--   $$L(X)=-\int_0^\infty F_X(t)\log F_X(t)\,dt .$$
--   Then
--   $$L(h(V))\le\sum_{j=1}^m\mathbb E_{V_{-j}}\big[L(h(V_{-j},V_j))\big],$$
--   where in each summand $L$ is computed over $V_j$ with $V_{-j}$ fixed, and the outer expectation averages over $V_{-j}$.
--
--   This is the coordinatewise bound for $L$ used on the residual $w$ in the proof of Theorem 4.3.
--
--   **Formalization Note** $L$ is an integral of the nonnegative function $-F\log F$ over $t\ge0$, valued in $[0,\infty]$, so no integrability side condition is needed. Boundedness and nonnegativity of $h(V)$ are assumed almost surely, the property of the random variable; $h$ is a measurable function of $V$.
--
--   Differences from the source:
--   - generalization: V = (V_1, …, V_m) with independent coordinates (real valued in every use) → a finite index type and coordinates in arbitrary measurable spaces α j with probability laws ν j, V distributed as Measure.pi ν; reason: every real or nonnegative coordinate setting is the special case α j = ℝ or ℝ≥0; the statement is purely measure theoretic
--   - encoding: E_{V−j}[· computed over V_j with V−j fixed] → outer integral over the full product law of the slice x ↦ (function of Function.update v j x); reason: the slice does not depend on v_j, so integrating it against the product law equals averaging over V_{−j}
--   - reading: h(V) is bounded and nonnegative → ∃ C, almost surely 0 ≤ h(V) ≤ C under the product law, with h measurable; reason: the hypothesis is a property of the random variable h(V); the almost-sure reading is the stronger lemma and contains the pointwise one
--   - encoding: L(X) = −∫_0^∞ F_X(t) log F_X(t) dt for bounded X ≥ 0 → cumulativeEntropy of the law of X, a [0,∞]-valued lintegral of ENNReal.ofReal(−F log F) over t ≥ 0; reason: the integrand is nonnegative since 0 ≤ F ≤ 1, so the extended value equals the real one for bounded X and needs no integrability condition
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 13, Lemma 4.2 (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_Supplement_Entropy
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling.Supplement

theorem lemma_4_2 {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type}
    [∀ j, MeasurableSpace (α j)] (ν : ∀ j, Measure (α j)) [∀ j, IsProbabilityMeasure (ν j)]
    (h : (∀ j, α j) → ℝ) (hh : Measurable h)
    (hbdd : ∃ C : ℝ, ∀ᵐ v ∂Measure.pi ν, 0 ≤ h v ∧ h v ≤ C) :
    cumulativeEntropy ((Measure.pi ν).map h) ≤
      ∑ j, ∫⁻ v, cumulativeEntropy ((ν j).map (fun x => h (Function.update v j x)))
        ∂Measure.pi ν := by sorry


end BulowKlemperer429.Bundling.Supplement
