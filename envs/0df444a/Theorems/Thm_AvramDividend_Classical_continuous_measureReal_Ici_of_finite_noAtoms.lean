-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuous_measureReal_Ici_of_finite_noAtoms
-- name    : AvramDividend.Classical.continuous_measureReal_Ici_of_finite_noAtoms
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T13:32:38.153828+00:00
-- url     : https://prove2.me/theorems/8ed92bad-b2fd-4237-9097-5c2176b40ae9
-- title:
--   Atomless finite upper-tail mass is continuous
-- statement:
--   If a measure on the real line has no singleton atoms and every upper interval [x,∞) has finite mass, then its real-valued tail mass x↦μ([x,∞)) is continuous. This is the deterministic continuity step appearing in excursion-height representations of derivatives of spectrally negative Lévy scale functions.
-- source:
--   Pinned Mathlib MeasureTheory.IntegrableOn.continuousOn_Ici_primitive_Ici and setIntegral_one_eq_measureReal; source-neutral helper for Avram scale-function regularity.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.continuous_measureReal_Ici_of_finite_noAtoms
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ x : ℝ, μ (Ici x) ≠ ⊤) :
    Continuous (fun x : ℝ => μ.real (Ici x)) := by sorry
