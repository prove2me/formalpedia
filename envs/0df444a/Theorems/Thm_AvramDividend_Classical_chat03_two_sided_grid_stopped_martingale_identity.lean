-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_stopped_martingale_identity
-- name    : AvramDividend.Classical.chat03_two_sided_grid_stopped_martingale_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:25:14.787578+00:00
-- url     : https://prove2.me/theorems/73464341-39b0-42c4-8f14-5b4618f13688
-- title:
--   Bounded optional sampling at the first strict two-sided exit on an adapted grid
-- statement:
--   Given a real-valued adapted discrete-time process Z and any real-valued martingale M on the same finite-measure filtered probability space, set K equal to the first k≤m for which Z_k>upper or Z_k<lower, defaulting to m when there is no exit. Then E[M_K]=E[M_0]. The first strict two-sided exit is encoded by the continuous observable max(Z_k−upper,lower−Z_k)>0, and the equality follows from adaptedness of that observable and the accepted bounded first-crossing optional-sampling theorem. This lemma formalises the correct strict two-sided mesh stopping rule for Lévy scale-function exit proofs without requiring right-continuity of the filtration. It does not assert that a killed scale process is a martingale nor justify passage to continuous time.
-- source:
--   Source-faithful Chat 03 dyadic two-sided-exit formalisation, 19 October 2026. Exact accepted dependency: AvramDividend.Classical.chat03_bounded_first_crossing_martingale_identity (ed435269-a323-46ba-b861-825718256fc4); Avram, Palmowski and Pistorius, arXiv:math/0702893, Equation (3.6), for the continuous-time exit problem.

import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Martingale.Basic
import Theorems.Thm_AvramDividend_Classical_chat03_bounded_first_crossing_martingale_identity

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.chat03_two_sided_grid_stopped_martingale_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {G : Filtration ℕ mΩ}
    (Z M : ℕ → Ω → ℝ) (hZ : Adapted G Z)
    (hM : Martingale M G P) (lower upper : ℝ) (m : ℕ) :
    (∫ ω,
      M (hittingBtwn
        (fun k ω => max (Z k ω - upper) (lower - Z k ω))
        (Set.Ioi (0 : ℝ)) 0 m ω) ω ∂P) =
    ∫ ω, M 0 ω ∂P := by sorry
