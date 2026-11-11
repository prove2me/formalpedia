-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin33_finite_negative_activity_sfinite
-- name    : AvramDividend.Classical.avram_mix_fin33_finite_negative_activity_sfinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:24:20.338362+00:00
-- url     : https://prove2.me/theorems/2025dae5-1cca-4ca4-a67e-cf6f69d05aba
-- title:
--   Finite negative Lévy activity supplies the s-finite product-mark hypothesis
-- statement:
--   For any Borel measure ν on the real line with finite intensity on negative marks, the restricted negative-mark measure is finite and hence s-finite. This discharges exactly the typeclass assumption used by the proven original product-measure Fubini lemma and the new ruin-stopped Taylor product-L1 bridge in the finite mixed branch. No first absolute mark moment is assumed.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin33_finite_negative_activity_sfinite
    (ν : Measure ℝ) (hν : ν (Iio (0 : ℝ)) ≠ ⊤) :
    SFinite (ν.restrict (Iio (0 : ℝ))) := by sorry
