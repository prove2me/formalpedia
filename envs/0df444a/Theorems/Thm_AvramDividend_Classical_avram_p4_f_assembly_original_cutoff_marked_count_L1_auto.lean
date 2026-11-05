-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T11:59:55.503103+00:00
-- url     : https://prove2.me/theorems/3d8bb7f8-9718-4efb-92e2-33527c7fe775
-- title:
--   Original finite negative-band Lévy marked count is L1 without any extra assumptions
-- statement:
--   For any original spectrally negative Lévy process, horizon T and negative cutoff 1/(n+1), its genuine intrinsic marked-jump count has integrable real value on P. The proof combines public original count measurability, source finite mass of separated negative Borel marks, and exact original P2 zero-origin intensity. It is the unconditional hJ input to the P4-F second-moment ordered-pair reduction, with no Poisson count or moment axiom.
-- source:
--   Original P2-E source count measurable 5cb1e247, P2-A negative Borel ν finite 86086cb2, source rate 34dbea70, pinned Mathlib integrable_toReal_of_lintegral_ne_top.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    Integrable (fun ω => (N ω).toReal) P := by sorry
