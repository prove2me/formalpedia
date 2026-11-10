-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_phys16_original_firstjump_straddling_cash_atom_split
-- name    : AvramDividend.Classical.avram_bv_phys16_original_firstjump_straddling_cash_atom_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T13:49:41.545175+00:00
-- url     : https://prove2.me/theorems/953d68c4-642e-4065-9e60-ca9e2dfa0e51
-- title:
--   Original first-negative-jump zero-contact straddling cell splits drift cash and endpoint atom
-- statement:
--   For the original finite-activity BV dividend process, a zero post-right-payment reserve on the whole strict interval before the first negative source jump gives exact arbitrary weighted drift cash there. The half-open cell ending at that jump splits exactly into this strict interior drift-volume cash plus the original Stieltjes dividend singleton at the jump. The singleton is explicit rather than silently counted as strict pre-ruin cash, and the same almost-sure event works for all eligible intervals and exhausting prefixes.
-- source:
--   Source-exact ruin-straddling last-cell subledger for 2bc848f9 and finite-activity original physical witness 8271cf4d; Proved c193be03 plus pinned Mathlib lintegral_union.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_strict_prejump_zero_cash_of_first_source_jump
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_phys16_original_firstjump_straddling_cash_atom_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (hH : 0 < H) :
    ∀ᵐ ω ∂P, ∀ (s J : ℝ≥0), s < J → J ≤ H →
      (J : WithTop ℝ≥0) ≤
        (⨅ u : ℝ≥0,
          if 0 < u ∧ X.X u ω -
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
      (∫⁻ t in Ioc (s : ℝ) (J : ℝ), f t
        ∂(dividendMeasure D ω)) =
      (∫⁻ t in Ioo (s : ℝ) (J : ℝ), f t
        ∂((ENNReal.ofReal X.drift) • volume)) +
      (∫⁻ t in ({(J : ℝ)} : Set ℝ), f t
        ∂(dividendMeasure D ω)) := by sorry
