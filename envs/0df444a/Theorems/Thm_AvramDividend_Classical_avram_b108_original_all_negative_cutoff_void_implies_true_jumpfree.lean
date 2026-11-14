-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b108_original_all_negative_cutoff_void_implies_true_jumpfree
-- name    : AvramDividend.Classical.avram_b108_original_all_negative_cutoff_void_implies_true_jumpfree
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T16:01:40.6226+00:00
-- url     : https://prove2.me/theorems/b7d035a9-c2d8-461d-9b8e-085fa95f05f4
-- title:
--   Absence of all genuine negative Lévy cutoff bands implies truly jumpfree original source interval on a no-positive-jump path
-- statement:
--   On the genuine original Levy source sample path, assume every physical source jump in the half-open interval (s,t] is nonpositive and that none belongs to any prescribed cofinal negative mark band at most -1/(n+1). If a nonzero source jump existed it would be negative, and its strictly positive magnitude would exceed a reciprocal cutoff at some n by convergence to zero, contradicting the no-band hypothesis. Therefore every original source jump increment on the true interval is zero. This is an exact source pathwise condition to discharge the nojump premises of compensated small and large mark increment theorems, keeping the absence-of-positive-jump assumption explicit.
-- source:
--   Original physical Levy mark sign and Mathlib tendsto_one_div_add_atTop_nhds_zero_nat.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Absence of every original negative cutoff source mark gives genuine jumpfree intervals on paths with no positive jumps. -/

theorem AvramDividend.Classical.avram_b108_original_all_negative_cutoff_void_implies_true_jumpfree
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0)
    (hNoPos : ∀ u : ℝ≥0, s < u → u ≤ t →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ 0)
    (hNoBand : ∀ n : ℕ, ∀ u : ℝ≥0, s < u → u ≤ t →
      ¬ (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1)))) :
    ∀ u : ℝ≥0, s < u → u ≤ t →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by sorry
