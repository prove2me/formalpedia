-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_all_negative_mark_envelope_exists_from_actual_smoothness
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_C1_all_negative_mark_envelope_exists_from_actual_smoothness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:15:47.116101+00:00
-- url     : https://prove2.me/theorems/73076122-e5bb-48ff-94b3-f78cffe4ef52
-- title:
--   Existence of full negative Lévy-mark BV C1 first-variation and large-mark envelope directly from original candidate smoothness
-- statement:
--   For the genuine original bounded-variation Levy controlled source and its C1 verification candidate continuous on nonnegative reserves and zero below ruin, plus actual compact positive-cap C1 derivative ceiling K on [a/2,b], construct a finite nonnegative R and prove for EVERY original predictable left reserve in [a,b] and EVERY negative original Levy mark z the exact absolute discounted nonlinear source jump bound by L(-z) at small marks and 2R at large marks. The local Lipschitz and global below-reserve value bounds are both derived from the original candidate continuity/C1 hypotheses, with no added Lipschitz or global value-bound axiom. Retains source-before-dividend chronology and crossing of ruin.
-- source:
--   Compose original BV compact C1 derivative Lip 82f28985, the published W7-02 global candidate below-ceiling bound and accepted original full negative-mark C1 pointwise piecewise envelope 2b420992.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_C1_verification_candidate_uniform_below_finite_reserve_ceiling
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_C1_full_negative_source_mark_discounted_piecewise_variation_envelope
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_C1_all_negative_mark_envelope_exists_from_actual_smoothness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b)
    (hOpen : IsOpen {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hBandSmooth : Icc (a / 2) b ⊆
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (K : ℝ≥0)
    (hK : ∀ v ∈ Icc (a / 2) b, ‖deriv w v‖₊ ≤ K) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ (ω : Ω) (t : ℝ≥0),
        Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t ∈ Icc a b →
        ∀ z : ℝ, z < 0 →
          |Real.exp (-(q * (t : ℝ))) *
            (w (Function.leftLim (fun s : ℝ≥0 =>
              x + X.X s ω - rightLimit D s ω) t + z) -
             w (Function.leftLim (fun s : ℝ≥0 =>
              x + X.X s ω - rightLimit D s ω) t))| ≤
            if z ≤ -a / 2 then 2 * R else (K : ℝ) * (-z) := by sorry
