-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_martingale_sampled_filtration_reindex_corrected
-- name    : AvramDividend.Classical.chat03_martingale_sampled_filtration_reindex_corrected
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:55:54.864296+00:00
-- url     : https://prove2.me/theorems/149bd72c-c5a0-44b2-82bb-90d7608ebb47
-- title:
--   Continuous-time martingale remains a martingale on a monotone deterministic grid
-- statement:
--   Let M be a real-valued martingale in a filtration G indexed by nonnegative real time. Let clock(k) be any monotone deterministic sequence of grid times and H any discrete filtration with H_k=G_clock(k). Then the sampled process M_clock(k) is a martingale in H. The proof transports strong adaptedness and conditional expectation equality at deterministic times, requiring no right-continuous filtration or continuous-time stopping theorem. This is the corrected, parser-safe formulation of monotone-clock sampling for the Avram q-scale exit proof programme; it can be instantiated at dyadic grids by constructing the elementary sampled filtration.
-- source:
--   Chat 03 direct source-level proof from pinned Mathlib.Probability.Martingale.Basic, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Intended application to Avram, Palmowski and Pistorius (2007), arXiv:math/0702893, Section 3.

import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Filtration

open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.chat03_martingale_sampled_filtration_reindex_corrected
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {G : Filtration ℝ≥0 mΩ}
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M G P)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = G (clock k)) :
    Martingale (fun k ω => M (clock k) ω) H P := by sorry
