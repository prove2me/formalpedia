-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_shift_convex_strictMonoOn
-- name    : AvramDividend.Classical.esscher_shift_convex_strictMonoOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:36:46.034073+00:00
-- url     : https://prove2.me/theorems/889c0779-4020-49f8-8c77-37d1f296261d
-- title:
--   Positive Esscher root and convexity force shifted-exponent strict increase
-- statement:
--   Given a real convex Laplace-exponent candidate psi on [0,∞) with psi(0)=0, and phi>0, q>0 satisfying psi(phi)=q, show beta↦psi(phi+beta)−q strictly increases on beta≥0. This is the generic source-faithful convexity bridge needed for the positive Esscher root asymptotic package; applying it to the canonical spectrally-negative Lévy exponent additionally requires its actual convexity theorem.
-- source:
--   Pinned Mathlib.Analysis.Convex.Slope.ConvexOn.strictMonoOn; Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes, Laplace exponent and positive root sections.

import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
open Set

theorem AvramDividend.Classical.esscher_shift_convex_strictMonoOn
    (psi : ℝ → ℝ) (phi q : ℝ)
    (hconv : ConvexOn ℝ (Ici (0 : ℝ)) psi)
    (hpsi0 : psi 0 = 0) (hphi : 0 < phi)
    (hq : 0 < q) (hpsiphi : psi phi = q) :
    StrictMonoOn (fun beta : ℝ => psi (phi + beta) - q) (Ici 0) := by sorry
