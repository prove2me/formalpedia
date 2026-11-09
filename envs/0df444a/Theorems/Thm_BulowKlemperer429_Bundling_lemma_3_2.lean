-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_lemma_3_2
-- name    : BulowKlemperer429.Bundling.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:18.351085+00:00
-- url     : https://prove2.me/theorems/c91ffc95-5215-4636-8502-3b1ecec41b0b
-- title:
--   Lemma 3.2 — scalar variation is covered by the right derivative
-- statement:
--   Let $X\sim F$ be nonnegative with concave revenue curve. Let $g:[0,\infty)\to\mathbb R$ be bounded, nondecreasing, concave and $1$-Lipschitz. Its right derivative exists and is nonnegative at every $x\ge0$, and
--   $$G(g(X))\le\mathbb E[Xg'_+(X)].$$
--   This is the scalar regularity comparison used for each coordinate of the residual. No density or atomlessness is required.
--
--   **Formalization Note** Both sides are real integrals: boundedness makes $g(X)$ integrable, and concavity gives $0\le xg'_+(x)\le g(x)-g(0)$, so the right integrand is bounded and integrable even when $X$ has infinite mean.
--
--   Differences from the source:
--   - encoding: finite monopoly revenue assumed throughout → no separate finite-revenue hypothesis for regular marginals; reason: the nonnegative concave revenue curve is bounded on (0,1), which implies finite posted-price revenue
--   - encoding: right derivatives on [0,∞), including zero → derivWithin g (Ioi x) x, with existence stated explicitly; reason: concavity and the Lipschitz bound give the right derivative everywhere on the half-line; the extension below zero is unused
--   - encoding: g is defined on [0,∞) → a real function g with all hypotheses restricted to Ici 0; reason: any source function extends to the real line and no value at a negative argument is used
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 8, Lemma 3.2 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_Revenue
import Definitions.Def_BulowKlemperer429_Bundling_Variation
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling

theorem lemma_3_2 (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (hreg : IsRegular ν) (g : ℝ → ℝ)
    (hbounded : ∃ C : ℝ, ∀ x ∈ Set.Ici (0 : ℝ), |g x| ≤ C)
    (hmono : MonotoneOn g (Set.Ici 0))
    (hconcave : ConcaveOn ℝ (Set.Ici 0) g)
    (hlip : LipschitzOnWith 1 g (Set.Ici 0)) :
    variation ν (fun x => g (x : ℝ)) ≤
      ∫ x : ℝ≥0, (x : ℝ) * rightDeriv g (x : ℝ) ∂ν ∧
    (∀ x ∈ Set.Ici (0 : ℝ), HasDerivWithinAt g (rightDeriv g x) (Set.Ioi x) x ∧
      0 ≤ rightDeriv g x) := by sorry

end BulowKlemperer429.Bundling
