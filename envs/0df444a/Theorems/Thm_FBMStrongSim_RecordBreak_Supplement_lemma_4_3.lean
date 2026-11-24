-- Prove2me | Theorems.Thm_FBMStrongSim_RecordBreak_Supplement_lemma_4_3
-- name    : FBMStrongSim.RecordBreak.Supplement.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:30:51.5628+00:00
-- url     : https://prove2.me/theorems/f15207a4-ceeb-43de-b367-6de6da1379dd
-- title:
--   Lemma 4.3 — Both signed likelihood bounds
-- statement:
--   For fBM with $0<H<1$, $0<\delta<H$, and $\rho>0$, fix $n\ge N^*(\rho,\delta)$. Almost every realized level-$n$ input satisfying BCE has the following property for every $m\ge1$, $1\le k\le2^{n+m-1}$, and candidate dyadic path $v$:
--   $$b_{n+m,k}(v)>\rho\ell_{n+m}\Longrightarrow\Theta_n^+(m,k)(v)\le1,$$
--   $$b_{n+m,k}(v)<-\rho\ell_{n+m}\Longrightarrow\Theta_n^-(m,k)(v)\le1.$$
--   All quantities are computed under the actual conditional law and the proposal distribution in SamplingModel. These bounds make the rejection step a valid acceptance probability.
--
--   Differences from the source:
--   - encoding: P_n(·)=P(·|B_n) at realized input values → condDistrib evaluated at levelValues B n ω, with the conditional conclusions for P-almost every ω; reason: regular conditional laws are specified only almost everywhere; the kernel is computed from B and P
--   - generalization: the continuous fBM version → every process satisfying the published IsFBM coordinate-law model, without a path-continuity premise in Section 4; reason: these algorithm laws use only the countable dyadic coordinates, whose joint law agrees with the continuous version; no source process is excluded
--   - encoding: Θ times the crossing indicator is at most one → on the crossing event Θ is at most one; reason: outside the event the indicator product is zero, so the two forms are equivalent
--   - reading: the density ψ and the plus sign in the first displayed line defining Θ− (pp. 17–18) → measure tilting, with the negative signed parameter for Θ−; reason: known dyadic endpoints can make the Gaussian singular; the negative-tilt second line of the source fixes the sign
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 19, Lemma 4.3

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_SamplingModel

namespace FBMStrongSim.RecordBreak.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Lemma 4.3 (p.19), both crossing signs, on every candidate path. -/
theorem lemma_4_3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {H delta rho : ℝ} (hH0 : 0 < H) (hH1 : H < 1) (hd0 : 0 < delta)
    (hdH : delta < H) (hrho : 0 < rho) {B : ℝ → Ω → ℝ} (hB : IsFBM H B P)
    (n : ℕ) (hn : startLevel rho delta ≤ n) :
    ∀ᵐ ω ∂P, let mu := conditionalLaw B P n (levelValues B n ω)
      BCE mu rho H delta n → ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, 1 ≤ k →
        k ≤ 2 ^ (n + m - 1) → ∀ v : DyadicPath,
          (Crossing rho H delta (n + m) k true v →
            weightedRatio mu rho H delta n m k true v ≤ 1) ∧
          (Crossing rho H delta (n + m) k false v →
            weightedRatio mu rho H delta n m k false v ≤ 1) := by sorry

end FBMStrongSim.RecordBreak.Supplement
