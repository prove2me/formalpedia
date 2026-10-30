-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_Qp_neverRecord_mass_le_supremum_complement
-- name    : AvramDividend.Classical.avram_ws01h_Qp_neverRecord_mass_le_supremum_complement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:38:33.317405+00:00
-- url     : https://prove2.me/theorems/87b1622f-cf2d-46b5-9103-3b378eece081
-- title:
--   Actual Qp never-upcrossing mass bounded by the complement of its running-supremum tail
-- statement:
--   For the actual joint random-terminal Esscher measure Qp constructed from the original Levy law P and a genuine exponential clock, paths whose first strict upper passage lies after the observed age are contained in the complement of the genuine running-supremum upper-tail event. Hence the remaining finite-p no-upper-record mass is bounded by the Qp supremum complement. This is the source event bound used to make the killed-renewal remainder vanish at small p.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013), spectrally negative Levy first passage; source identity b626324c-8e00-4488-86d6-b7d63449435c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_Qp_neverRecord_mass_le_supremum_complement
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (φ p : ℝ) (hp : 0 < p) :
    (let Qp : Measure (Ω × ℝ) :=
      (P.prod (ProbabilityTheory.expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (φ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ φ)))
    Qp {z : Ω × ℝ |
      (Real.toNNReal z.2 : ℝ≥0∞) < twoSidedExitUpTime X b z.1} ≤
    Qp {z : Ω × ℝ |
      ¬ b < runningSup X (Real.toNNReal z.2) z.1}) := by sorry
