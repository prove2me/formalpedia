-- Prove2me | Theorems.Thm_ConnesGreen_primeOverlapLoss_continuous
-- name    : ConnesGreen.primeOverlapLoss_continuous
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T03:01:21.859057+00:00
-- url     : https://prove2.me/theorems/8fe7f09a-fe05-4113-853c-39268c31f5a8
-- title:
--   Prime overlap loss is continuous across every support threshold
-- statement:
--   For every FIXED complex function $g$, the scalar arithmetic loss budget $$T\longmapsto L_T(g)=\sum_{n\in A_T}\frac{2\Lambda(n)}{\sqrt n}\min(M(g),2E(g)\max(2T-\log n,0))$$ is continuous on $\mathbb R$. Although the original strict active prime set changes at prime-power thresholds, the entering overlap term is exactly zero at its threshold. This is continuity of an auxiliary arithmetic budget for a fixed function; it does not assert convergence of moving test functions, selected operators, or positivity certificates.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/PrimeOverlapMass.lean, exact declaration ConnesGreen.primeOverlapLoss_continuous, compiling local source 495a9f34f25d1dbfbeb6ba8dce6d4735559ae878. Original arithmetic definitions, physical energy, actual prime powers and admissible test class retained.

import Definitions.Def_ConnesGreen_prime_overlap_loss
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen

theorem ConnesGreen.primeOverlapLoss_continuous (g : ℝ → ℂ) :
    Continuous (fun T : ℝ => primeOverlapLoss T g) := by sorry
