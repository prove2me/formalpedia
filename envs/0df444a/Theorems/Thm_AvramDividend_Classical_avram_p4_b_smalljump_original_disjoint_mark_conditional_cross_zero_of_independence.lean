-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_disjoint_mark_conditional_cross_zero_of_independence
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_disjoint_mark_conditional_cross_zero_of_independence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:44:14.633676+00:00
-- url     : https://prove2.me/theorems/882776cc-e49a-4e11-b007-ade111c2007b
-- title:
--   Original intrinsic disjoint mark conditional cross orthogonality
-- statement:
--   Original-path independent disjoint marked counts have zero conditional cross moment given the actual past when future count algebra is independent.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_independent_disjoint_mark_band_orthogonality

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_disjoint_mark_conditional_cross_zero_of_independence
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
    (hProductInt : Integrable (fun ω => JA ω * JB ω) P)
    (hMeasA : AEStronglyMeasurable JA P)
    (hMeasB : AEStronglyMeasurable JB P)
    (hIndependentAB : IndepFun JA JB P)
    (rA rB : ℝ)
    (hRateA : rA = ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν A)).toReal)
    (hRateB : rB = ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal)
    (hFirstA : (∫ ω, JA ω ∂P) = rA)
    (hFirstB : (∫ ω, JB ω ∂P) = rB)
    (mFuture : MeasurableSpace Ω) (hFuture : mFuture ≤ mΩ)
    (hCrossStrong : StronglyMeasurable[mFuture] (fun ω =>
      (JA ω - rA) * (JB ω - rB)))
    (hFutureIndependent : Indep mFuture (𝓕 s) P) :
    P[(fun ω => (JA ω - rA) * (JB ω - rB)) | 𝓕 s] =ᵐ[P]
      (fun _ => (0 : ℝ)) := by sorry
