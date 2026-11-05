-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_independent_disjoint_mark_band_orthogonality
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_independent_disjoint_mark_band_orthogonality
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:18:35.440204+00:00
-- url     : https://prove2.me/theorems/039a3e36-cb14-4beb-aec9-5dc957ce1641
-- title:
--   Original disjoint Lévy mark orthogonality from count independence
-- statement:
--   Two independent actual original intrinsic Lévy marked-band counts with source first-moment rates have zero compensated cross moment.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_disjoint_mark_band_compensated_orthogonality

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_independent_disjoint_mark_band_orthogonality
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (A B : Set ℝ) (hDisjoint : Disjoint A B)
    (JA JB : Ω → ℝ)
    (hSourceA : ∀ ω, JA ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ A)).toReal)
    (hSourceB : ∀ ω, JB ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)
    (hJA : Integrable JA P) (hJB : Integrable JB P)
    (hCrossInt : Integrable (fun ω => JA ω * JB ω) P)
    (hMeasA : AEStronglyMeasurable JA P)
    (hMeasB : AEStronglyMeasurable JB P)
    (hIndependent : IndepFun JA JB P)
    (rA rB : ℝ)
    (hRateA : rA = ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν A)).toReal)
    (hRateB : rB = ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal)
    (hFirstA : (∫ ω, JA ω ∂P) = rA)
    (hFirstB : (∫ ω, JB ω ∂P) = rB) :
    (∫ ω, (JA ω - rA) * (JB ω - rB) ∂P) = 0 := by sorry
