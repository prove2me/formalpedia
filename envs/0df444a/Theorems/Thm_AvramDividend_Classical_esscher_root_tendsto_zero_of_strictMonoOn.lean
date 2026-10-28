-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_root_tendsto_zero_of_strictMonoOn
-- name    : AvramDividend.Classical.esscher_root_tendsto_zero_of_strictMonoOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:25:31.271031+00:00
-- url     : https://prove2.me/theorems/e746f729-2b86-4a36-961f-c65553d3ba44
-- title:
--   Positive root family of a strictly increasing exponent tends to zero with its level
-- statement:
--   A positive root family root(p) of a strictly increasing real function g on the nonnegative half-line, satisfying g(0)=0 and g(root(p))=p for p>0, converges to zero from the right as p decreases to zero. Pinned imports now include a real-analysis module defining ℝ. The input existence and Lévy specialisation remain separate.
-- source:
--   Elementary monotone inverse continuity and Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions, §2.1. Replacement for failed publication ed693bf9 (ℝ unknown; earlier v3 preamble had only topology/order imports).

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.NhdsWithin
import Mathlib.Order.Monotone.Basic
open Filter Set

theorem AvramDividend.Classical.esscher_root_tendsto_zero_of_strictMonoOn
    (g root : ℝ → ℝ)
    (hzero : g 0 = 0)
    (hmono : StrictMonoOn g (Ici (0 : ℝ)))
    (hpos : ∀ p : ℝ, 0 < p → 0 < root p)
    (hroot : ∀ p : ℝ, 0 < p → g (root p) = p) :
    Tendsto root (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhdsWithin (0 : ℝ) (Ioi 0)) := by sorry
