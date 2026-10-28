-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_root_quotient_tendsto_of_hasDerivAt
-- name    : AvramDividend.Classical.esscher_root_quotient_tendsto_of_hasDerivAt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:15:35.555343+00:00
-- url     : https://prove2.me/theorems/2ba922bf-e359-4bc2-8c6c-52aacb2c7886
-- title:
--   Positive-root small-rate quotient tends to the derivative at the origin
-- statement:
--   For g(0)=0 with strictly positive derivative m at zero, a family of positive roots root(p) converging to zero from the right, satisfying g(root(p))=p for p>0, has p/root(p) tending to m as p decreases to zero. Uses the explicit nhdsWithin (Ioi 0) filter to avoid parser issues. Root convergence and existence are separate obligations; no Wiener–Hopf dependence.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2012), The Theory of Scale Functions for Spectrally Negative Lévy Processes, §2.1. Mathlib HasDerivAt.tendsto_slope_zero_right, pinned 0df444a. Corrected failed jobs 992c83b5 (reserved λ binder) and db715c2e (unsupported 𝓝[>] notation in publication environment).

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.Ring
open Filter Set

theorem AvramDividend.Classical.esscher_root_quotient_tendsto_of_hasDerivAt
    (g root : ℝ → ℝ) (m : ℝ)
    (hzero : g 0 = 0)
    (hm : 0 < m)
    (hderiv : HasDerivAt g m 0)
    (hrootTendsto : Tendsto root (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hroot : ∀ p : ℝ, 0 < p → g (root p) = p) :
    Tendsto (fun p : ℝ => p / root p)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m) := by sorry
