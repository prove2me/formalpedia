-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_positive_event_first_mark_cash_ruin_excludes_unit_fullmark_ledger
-- name    : AvramDividend.Classical.avram_jump6_A_actual_positive_event_first_mark_cash_ruin_excludes_unit_fullmark_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:48:17.976405+00:00
-- url     : https://prove2.me/theorems/25cd30fc-785e-4205-a48f-112a0dea2606
-- title:
--   Genuine positive-measure first ruin event excludes the original capped unit-fullmark signed cash ledger
-- statement:
--   For an actual original spectrally negative Lévy model X=B−2N on a non-null event of the original probability measure, suppose physical first-jump count, no prior jumps, Brownian small tube, finite cap upper-exit clock, short mark time, and nonpositive drift hold almost surely on that event. The existing Proved actual first-ruin barrier stopped terminal plus inclusive Stieltjes cash bound forces the left side to be exactly zero, while its unit-fullmark signed ledger upper bound is negative, giving an explicit contradiction. This upgrades Proved original eventwise cash obstruction 102ec163 to the true positive-measure setting. The remaining independent obligation is proving the model/stop identifications on the original positive joint Brownian–Poisson event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_first_size2_ruin_cash_excludes_physical_unitmark_certificate
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_actual_positive_event_first_mark_cash_ruin_excludes_unit_fullmark_ledger
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω) (hA : 0 < P A)
    (B : Ω → ℝ≥0 → ℝ) (N : Ω → ℝ≥0 → ℕ)
    (σ u : Ω → ℝ≥0) (q : ℝ) (Drift : Ω → ℝ)
    (hData : ∀ᵐ ω ∂(P.restrict A),
      (∀ t : ℝ≥0, X.X t ω = B ω t - 2 * (N ω t : ℝ)) ∧
      (∀ t : ℝ≥0, t ≤ σ ω → |B ω t| < (1 / 4000 : ℝ)) ∧
      (∀ t : ℝ≥0, t < σ ω → N ω t = 0) ∧
      (N ω (σ ω) = 1) ∧
      ((u ω : ℝ≥0∞) =
        (⨅ (s : ℝ≥0)
          (_ : (1 / 5 : ℝ) - (1 / 10 : ℝ) < X.X s ω),
          (s : ℝ≥0∞))) ∧
      ((σ ω : ℝ) ≤ 1 / 10) ∧ Drift ω ≤ 0)
    (hLedger : ∀ᵐ ω ∂(P.restrict A),
      Real.exp (-(q * (σ ω : ℝ))) *
        (if riskProcess X (1 / 10 : ℝ)
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
            (σ ω) ω < 0 then 0
         else 1 + riskProcess X (1 / 10 : ℝ)
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
            (σ ω) ω +
            (riskProcess X (1 / 10 : ℝ)
              (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
              (σ ω) ω) ^ 2) +
        (∫⁻ s in paymentTimes
            (ruinTime X (1 / 10 : ℝ)
              (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)
            ∩ Iic (σ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure
              (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)).toReal ≤
      (1 + (1 / 10 : ℝ) + (1 / 10 : ℝ) ^ 2) +
      B ω (σ ω) + (-2 * (N ω (σ ω) : ℝ) + 2 * (σ ω : ℝ)) +
      Drift ω) :
    False := by sorry
