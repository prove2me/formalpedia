-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_martingale_monotone_clock_reindex
-- name    : AvramDividend.Classical.chat03_martingale_monotone_clock_reindex
-- status  : Open
-- author  : @WillR
-- created : 2026-10-19T16:52:48.827464+00:00
-- url     : https://prove2.me/theorems/43fba27e-3756-41a3-b4bd-c5141f7334cb
-- title:
--   Monotone deterministic sampling of a continuous-time martingale preserves the martingale property
-- statement:
--   Let M_t be a real-valued martingale in a filtration G indexed by nonnegative real time. For any monotone sequence of deterministic grid times clock(k), the sampled discrete process M_clock(k) is a martingale relative to the pulled-back discrete filtration H_k=G_clock(k). The proof transfers strong adaptedness and every deterministic-time conditional-expectation identity directly from M, without assuming right-continuity of the filtration, a stopping-time property of continuous passage or a Markov theorem. This allows the already Proved compensated Lévy exponential martingale to be used with already Proved bounded-grid optional sampling in the exact Avram stopped-scale proof programme.
-- source:
--   Mathlib.Probability.Martingale.Basic at pinned 0df444a360eaa60ab8c11dca51a86af692955474, exact Martingale definition and condExp_ae_eq. Chat 03 direct proof development for Avram, Palmowski and Pistorius, arXiv:math/0702893, Section 3.

import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Filtration

open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.chat03_martingale_monotone_clock_reindex
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {G : Filtration ℝ≥0 mΩ}
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M G P)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) :
    Martingale (fun k ω => M (clock k) ω)
      ({ seq := fun k => G (clock k),
         mono' := fun _ _ h => G.mono (hc h),
         le' := fun _ => G.le _ } : Filtration ℕ mΩ) P := by sorry
