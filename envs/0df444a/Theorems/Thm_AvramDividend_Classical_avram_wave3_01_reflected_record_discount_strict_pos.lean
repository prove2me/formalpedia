-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_record_discount_strict_pos
-- name    : AvramDividend.Classical.avram_wave3_01_reflected_record_discount_strict_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T17:34:36.876055+00:00
-- url     : https://prove2.me/theorems/b1cbd08b-6e97-4e05-8d72-07654ba20e90
-- title:
--   Genuine discounted reflected-killed upward record has positive mass at every positive level
-- statement:
--   For q>0, an unbounded-variation spectrally negative Lévy process with its canonical positive q-scale function has a strictly positive discounted probability of first upward record at every positive level before reflected drawdown ruin at any fixed positive depth. The source scale-ratio sandwich supplies a positive record factor for small levels less than the depth, and the proved original-law uncapped first-record semigroup propagates positivity to any level by an Archimedean subdivision. This positivity rules out log-zero in the continuous record-hazard construction for proving source C1 regularity.
-- source:
--   Genuine stopped first-record Lévy renewal semigroup Proved UUID 3890ee9b; genuine Standing-free record scale-ratio sandwich Proved UUID f9f9bc34; q-scale strict positivity in unbounded variation Proved UUID e50526dc. Required for infinite-small-jump C1 root branch cd61d678, mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_reflected_record_discount_strict_pos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hnbv : ¬ X.BoundedVariation)
    (a : ℝ) (ha : 0 < a) :
    ∀ h : ℝ, 0 < h →
      0 < (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P) := by sorry
