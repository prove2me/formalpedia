-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_weighted_height_cdf_continuous
-- name    : AvramDividend.Classical.avram_wave3_01_weighted_height_cdf_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:56:44.401437+00:00
-- url     : https://prove2.me/theorems/fc5b5690-16f5-470e-9a92-0bda66a44b02
-- title:
--   Finite weighted real-height distribution is continuous at an atomless threshold
-- statement:
--   For any measurable real-valued height H, measurable nonnegative weight w with finite integral, and a threshold a at which the original measure has no H-atom, the weighted distribution integral E[w 1_{H≤b}] is continuous at b=a. This is the exact dominated-convergence tool needed to transfer canonical pure infinite-jump first-record reflected-height atomlessness into continuity of the actual killed first-record q-discount factor. The source application still requires measurable finite-record height and exact clock-survival equivalence.
-- source:
--   Mathlib Lebesgue nonnegative dominated convergence, original Lévy first-record positive-height atomlessness 35f216f9-e40c-4f5e-9c85-c4a5979d76ce, original path height survival 0b08ab70-9773-4d31-af46-34e4b37efd0c.

import Mathlib
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

open MeasureTheory Set Topology Filter
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave3_01_weighted_height_cdf_continuous
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : Ω → ℝ) (w : Ω → ℝ≥0∞)
    (hH : Measurable H) (hw : Measurable w)
    (hfinite : ∫⁻ ω, w ω ∂P ≠ ⊤)
    (a : ℝ) (hAtom : P {ω | H ω = a} = 0) :
    ContinuousAt
      (fun b : ℝ => ∫⁻ ω, if H ω ≤ b then w ω else 0 ∂P) a := by sorry
