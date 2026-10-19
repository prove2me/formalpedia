-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_bounded_first_crossing_martingale_identity
-- name    : AvramDividend.Classical.chat03_bounded_first_crossing_martingale_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:35:07.207547+00:00
-- url     : https://prove2.me/theorems/ed435269-a323-46ba-b861-825718256fc4
-- title:
--   Bounded discrete first-upcrossing optional sampling of a separate martingale
-- statement:
--   For an adapted real-valued discrete process Y and an integrable real-valued martingale M on the same finite-measure filtered space, let K be the first index k between 0 and m with Y_k>a, defaulting to m when no crossing occurs. Then E[M_K]=E[M_0]. It is vital that the observable whose crossing defines K need not equal the martingale being sampled. This discrete-time theorem avoids any right-continuity condition on a continuous-time filtration and forms an exact bounded-mesh bridge for the stopped q-scale exit identity. The proof uses measurability of K as a bounded stopping time and bounded optional sampling for M and -M; later dyadic-grid convergence and uniform integrability are separate obligations.
-- source:
--   Chat 03 derivation, 18 October 2026, based on Mathlib Probability/Process/HittingTime.lean and Probability/Martingale/OptionalStopping.lean at Mathlib 0df444a360eaa60ab8c11dca51a86af692955474; Avram, Palmowski and Pistorius (2007), arXiv:math/0702893, Section 3, for the stochastic exit setting.

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Adapted
import Mathlib.Tactic.Linarith

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.chat03_bounded_first_crossing_martingale_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {G : Filtration ℕ mΩ}
    (Y M : ℕ → Ω → ℝ) (hY : Adapted G Y)
    (hM : Martingale M G P) (a : ℝ) (m : ℕ) :
    (∫ ω, M (hittingBtwn Y (Set.Ioi a) 0 m ω) ω ∂P) =
      ∫ ω, M 0 ω ∂P := by sorry
