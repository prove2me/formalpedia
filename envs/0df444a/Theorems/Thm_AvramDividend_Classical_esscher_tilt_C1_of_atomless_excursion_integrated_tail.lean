-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_tilt_C1_of_atomless_excursion_integrated_tail
-- name    : AvramDividend.Classical.esscher_tilt_C1_of_atomless_excursion_integrated_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T23:28:44.330968+00:00
-- url     : https://prove2.me/theorems/fc875ce7-f8c6-47c4-a1d4-a7e9442ab904
-- title:
--   Atomless finite excursion-height tails yield Esscher-tilted C1 regularity
-- statement:
--   For an excursion-height measure with no atoms and finite upper tails above every positive level, its real tail is continuous on (0,∞). If a scale function is represented by the exponential of the integral of this tail from a positive anchor, and V is its Esscher tilt, then V is C1 on (0,∞). This isolates the deterministic consequence of excursion measure regularity for the no-standing Gaussian and infinite-variation Lévy cases. The measure may have infinite mass near zero.
-- source:
--   Kuznetsov, Kyprianou and Rivero, The Theory of Scale Functions, Lemma 2.4; deterministic composition of the already Proved atomless tail continuity, local interval FTC and Esscher-tilt transfer.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Ici_of_finite_pos_noAtoms
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_positive_integrated_excursion_tail
import Theorems.Thm_AvramDividend_Classical_esscher_tilt_contDiffOn_one_of_scale_contDiffOn_one
open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.esscher_tilt_C1_of_atomless_excursion_integrated_tail
    (μ : Measure ℝ) [NullSingletonClass μ] (W V : ℝ → ℝ)
    (a c φ : ℝ) (ha : 0 < a)
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤)
    (hW : ∀ x : ℝ, 0 < x →
      W x = c * Real.exp (∫ t in a..x, μ.real (Ici t)))
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by sorry
