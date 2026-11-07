-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn17_inhomogeneous_first_order_upper
-- name    : AvramDividend.Classical.avram_p4_f4_turn17_inhomogeneous_first_order_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:29:08.513907+00:00
-- url     : https://prove2.me/theorems/8101eff4-f1fd-4a1e-8c00-35ce56c93ec4
-- title:
--   Inhomogeneous first-order exponential upper comparison
-- statement:
--   An exponential forcing term with slower exponent is absorbed by adding B/(rpos-rneg) times a decaying comparison exponential; the resulting function satisfies the standard first-order exponential upper comparison.
-- source:
--   Exact integrating-factor reduction of factorised second-order Avram ODE positive-ray child.

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
open Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_turn17_inhomogeneous_first_order_upper
    (rpos rneg a : ℝ) (hgap : rneg < rpos) (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici a))
    (hwDiff : DifferentiableOn ℝ w (Ioi a))
    (B : ℝ) (hB : 0 ≤ B)
    (hDer : ∀ x : ℝ, a < x →
      deriv w x ≤ rpos * w x + B * Real.exp (rneg * (x - a))) :
    ∀ x : ℝ, a ≤ x →
      w x ≤ (w a + B / (rpos - rneg)) * Real.exp (rpos * (x - a)) := by sorry
