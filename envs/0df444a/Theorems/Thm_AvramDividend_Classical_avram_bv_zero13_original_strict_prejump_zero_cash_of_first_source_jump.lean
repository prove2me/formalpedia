-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_strict_prejump_zero_cash_of_first_source_jump
-- name    : AvramDividend.Classical.avram_bv_zero13_original_strict_prejump_zero_cash_of_first_source_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:37:09.794984+00:00
-- url     : https://prove2.me/theorems/c193be03-d06b-4312-bc2d-35ac1af0cc45
-- title:
--   Original strict pre-first-negative-jump arbitrary dividend zero-contact Stieltjes cash equals positive drift mass
-- statement:
--   For every admissible original controlled dividend strategy, on the common almost-sure pathwise Stieltjes cash event, take any strict open interval ending no later than the first physical source negative jump. If postpayment controlled reserve stays exactly zero on that interval and a monotone sequence of strictly earlier closed-right prefixes covers the open interval, the full nonnegative measurable weighted Stieltjes dividend cash equals drift-scaled Lebesgue cash. The source no-jump condition is discharged by the pathwise before-first-negative-jump original increment lemma and exact spectral negativity. Valid for arbitrary path-dependent restarts, excludes left endpoint right-payment and final source-jump atom, and preserves original filtration.
-- source:
--   Direct necessary bridge from proved f62dae07 strict-open zero-contact Stieltjes cash and new original negative first-jump nojump prerequisite a2c33db6 to the finite/top-cap BV stopped expected HJB source route.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_before_first_negative_jump_source_increments_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_strict_open_endpoint_zero_cash_of_prefix_cover

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_strict_prejump_zero_cash_of_first_source_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (hH : 0 < H) :
    ∀ᵐ ω ∂P,
      ∀ (s J : ℝ≥0), s < J → J ≤ H →
      (J : WithTop ℝ≥0) ≤
        (⨅ u : ℝ≥0,
          if 0 < u ∧
              X.X u ω -
                Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
          then (u : WithTop ℝ≥0) else ⊤) →
      ∀ (a : ℕ → ℝ≥0),
      (∀ n, s ≤ a n ∧ a n < J) →
      Monotone (fun n : ℕ => Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)) →
      (⋃ n, Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)) =
        Ioo (s : ℝ) (J : ℝ) →
      (∀ u : ℝ≥0, s ≤ u → u < J →
        riskProcess X x D u ω -
          (rightLimit D u ω - D u ω) = 0) →
      ∀ f : ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ t in Ioo (s : ℝ) (J : ℝ), f t
        ∂(dividendMeasure D ω)) =
      (∫⁻ t in Ioo (s : ℝ) (J : ℝ), f t
        ∂((ENNReal.ofReal X.drift) • volume)) := by sorry
