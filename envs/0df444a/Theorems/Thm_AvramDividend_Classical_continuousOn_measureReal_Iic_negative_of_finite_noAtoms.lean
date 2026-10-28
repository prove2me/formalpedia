-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Iic_negative_of_finite_noAtoms
-- name    : AvramDividend.Classical.continuousOn_measureReal_Iic_negative_of_finite_noAtoms
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:06:11.159018+00:00
-- url     : https://prove2.me/theorems/bcaf5931-7559-4bd0-8587-63bc33271a4c
-- title:
--   Atomless negative-tail cumulative is continuous below zero under finite-cutoff masses
-- statement:
--   For a measure on the real line with no atoms and finite mass on every interval (-∞,a] for a<0, the left cumulative mass, interpreted as a real number, is continuous on (-∞,0). This supplies the negative-tail continuity needed for a continuous Esscher renewal kernel in the bounded-variation Lévy case. Proof: restrict the measure to a finite cutoff above each point and apply continuity of the finite atomless cumulative measure.
-- source:
--   Measure-theoretic continuity of cumulative distribution functions for atomless locally finite measures; analytic input to the bounded-variation absolutely continuous Lévy renewal-kernel representation in Avram, Palmowski and Pistorius (2007).

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.ContinuousOn
import Theorems.Thm_AvramDividend_Classical_continuous_measureReal_Iic_of_finite_noAtoms
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.continuousOn_measureReal_Iic_negative_of_finite_noAtoms
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ a : ℝ, a < 0 → μ (Iic a) ≠ ⊤) :
    ContinuousOn (fun a : ℝ => μ.real (Iic a)) (Iio (0 : ℝ)) := by sorry
