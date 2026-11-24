-- Prove2me | Theorems.Thm_FBMStrongSim_RecordBreak_Supplement_lemma_3_7
-- name    : FBMStrongSim.RecordBreak.Supplement.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:29:34.591021+00:00
-- url     : https://prove2.me/theorems/51f4fc68-cbda-4910-bac8-50a929fa6ab1
-- title:
--   Lemma 3.7 — Level-increment Hölder bound
-- statement:
--   For any real path $x$, every $k\ge1$, and $0<\alpha\le1$, let $x_k$ be its dyadic linear interpolant and $D_k$ the largest absolute midpoint displacement at level $k$. Then
--   $$\|x_k-x_{k-1}\|_\alpha\le2^{\alpha(k-1)+2}D_k.$$
--   This deterministic estimate controls the individual terms in the Hölder error of the fBM interpolants.
--
--   Differences from the source:
--   - generalization: dyadic interpolants of fBM in the Hölder discussion → every real path and every 0<α≤1; reason: the interpolation bound depends only on finitely many values and specializes to every fBM sample path
--   - encoding: a homogeneous Hölder seminorm inequality → its pointwise increment inequality on [0,1]; reason: equivalent for positive α; it avoids a real supremum that defaults to zero on an unbounded set
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 13, Lemma 3.7

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_HolderModel

namespace FBMStrongSim.RecordBreak.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Lemma 3.7 (p.13), deterministic extension to 0<α≤1. -/
theorem lemma_3_7 (x : ℝ → ℝ) (k : ℕ) (hk : 1 ≤ k) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    HolderBound alpha ((2 : ℝ) ^ (alpha * ((k : ℝ) - 1) + 2) * maxDisp x k)
      (fun t => interp x k t - interp x (k - 1) t) := by sorry

end FBMStrongSim.RecordBreak.Supplement
