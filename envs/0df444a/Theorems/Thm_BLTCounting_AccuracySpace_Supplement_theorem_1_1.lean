-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_Supplement_theorem_1_1
-- name    : BLTCounting.AccuracySpace.Supplement.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:03:15.587929+00:00
-- url     : https://prove2.me/theorems/097448ca-b8f1-485c-9480-c1e44b2699e3
-- title:
--   Theorem 1.1 — Sharp leading inverse-polynomial BLT lower bound
-- statement:
--   For every fixed $\gamma\in(0,1]$ and every $\delta>0$ there is $n_0=n_0(\gamma,\delta)\ge1$ such that, for every $n\ge n_0$, every complex BLT sequence $c$ of recurrence order at most $d$ and every real $\eta$ satisfying $\|c-f\|_{\ell_2(0,n-1)}\le\eta\le n^{-\gamma}$,
--   $$d\ge\left({\gamma^2\over4\pi^2}-\delta\right)(\log n)^2.$$
--   Thus the sharp leading asymptotic is uniform over $c,d,\eta$. No positive lower bound on $\eta$ is imposed, and $\gamma=1$ is included. This is a companion result rather than a new proof obligation of Theorem 1.2.
--
--   Differences from the source:
--   - encoding: uniform −o(1) leading remainder as n tends to infinity → for each δ>0 one n₀ before all n,d,c,η; reason: this is the full sharp asymptotic, with no restriction on varying η
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Theorem 1.1, printed p. 2 (PDF p. 3)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_Supplement_Lattice

namespace BLTCounting.AccuracySpace.Supplement

/-- Theorem 1.1, PDF p.3. The threshold n₀ depends only on fixed γ and δ, not c,d,η.
All η with coeffErr ≤ η ≤ n^(-γ) are covered, including η=0. -/
theorem theorem_1_1 (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∀ (d : ℕ) (c : ℕ → ℂ) (η : ℝ), IsBLT d c →
        coeffErr n c sqrtSeq ≤ η → η ≤ (n : ℝ) ^ (-γ) →
        (γ ^ 2 / (4 * Real.pi ^ 2) - δ) * (Real.log n) ^ 2 ≤ (d : ℝ) := by sorry

end BLTCounting.AccuracySpace.Supplement
