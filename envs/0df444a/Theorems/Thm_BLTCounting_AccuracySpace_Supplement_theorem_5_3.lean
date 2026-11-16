-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_Supplement_theorem_5_3
-- name    : BLTCounting.AccuracySpace.Supplement.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:04:17.542096+00:00
-- url     : https://prove2.me/theorems/de3d39f6-dc8a-4cb9-8f2a-f165a8542459
-- title:
--   Theorem 5.3 — Rational degree obstruction and logarithmic-degree nonexistence
-- statement:
--   Put $\rho_n=e^{-1/n}$ and $F(z)=(1-z)^{-1/2}$, using the analytic branch on the unit disk with $F(0)=1$. There exist absolute $C>0$ and $n_0\ge1$ such that, for every $n\ge n_0$ and every complex rational function $r$, if $g=r/(1-z)$ has no pole on $|z|=\rho_n$ and
--   $$\frac1{2\pi}\int_{-\pi}^{\pi}|g(\rho_ne^{i\theta})-F(\rho_ne^{i\theta})|^2\,d\theta\le\frac1n,$$
--   then $\deg r\ge C(\log n)^2$. Degree means the maximum of numerator and denominator degrees after cancellation.
--
--   Consequently no family $(r_n)$ can satisfy this second approximation condition for every sufficiently large $n$ while having $\deg r_n\le A\log n$ for one finite constant $A>0$. Both conclusions are included. Interior and multiple poles are allowed; the first approximation condition of the cited conjecture is not assumed.
--
--   Differences from the source:
--   - encoding: degree Ω(log² n), consequently no degree O(log n) eventual family → one positive lower-bound constant and threshold before n,r, and the explicit negation of an eventual logarithmic-degree family; reason: these spell out both uniform asymptotic statements without added approximation hypotheses
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Theorem 5.3, printed p. 32 (PDF p. 33)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_Supplement_CircleApproximation

namespace BLTCounting.AccuracySpace.Supplement

/-- Theorem 5.3, PDF p.33, including its nonexistence consequence.
The uniform degree lower bound applies to all rational functions, without excluding interior poles.
The only approximation condition is E₂,n ≤ 1/n; no condition on E₁,n is added. -/
theorem theorem_5_3 :
    (∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∀ r : RatFunc ℂ, NoPoleOnCircle (dividedApprox r) (circleRadius n) →
        circleError (dividedApprox r) (circleRadius n) ≤ 1 / (n : ℝ) →
        C * (Real.log n) ^ 2 ≤ (rationalDegree r : ℝ)) ∧
    ¬ (∃ (r : ℕ → RatFunc ℂ) (C : ℝ), 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n →
        NoPoleOnCircle (dividedApprox (r n)) (circleRadius n) ∧
        circleError (dividedApprox (r n)) (circleRadius n) ≤ 1 / (n : ℝ) ∧
        (rationalDegree (r n) : ℝ) ≤ C * Real.log n) := by sorry

end BLTCounting.AccuracySpace.Supplement
