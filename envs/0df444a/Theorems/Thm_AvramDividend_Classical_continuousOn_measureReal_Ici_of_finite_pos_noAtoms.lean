-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Ici_of_finite_pos_noAtoms
-- name    : AvramDividend.Classical.continuousOn_measureReal_Ici_of_finite_pos_noAtoms
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T17:42:10.120982+00:00
-- url     : https://prove2.me/theorems/432e2de3-ff04-4007-a152-32192ab4b868
-- title:
--   Atomless upper-tail mass is continuous on the positive half-line under positive-tail finiteness
-- statement:
--   For an atomless measure, it is enough that each strictly positive upper tail [x,∞) has finite mass to obtain continuity of the real-valued tail function on (0,∞). No finiteness at zero or on negative thresholds is required. This is the correct deterministic hypothesis for excursion-height measures, which can have infinite total mass.
-- source:
--   Local application of pinned Mathlib IntegrableOn.continuousOn_Ici_primitive_Ici and setIntegral_one_eq_measureReal.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.continuousOn_measureReal_Ici_of_finite_pos_noAtoms
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) :
    ContinuousOn (fun x : ℝ => μ.real (Ici x)) (Ioi 0) := by sorry
