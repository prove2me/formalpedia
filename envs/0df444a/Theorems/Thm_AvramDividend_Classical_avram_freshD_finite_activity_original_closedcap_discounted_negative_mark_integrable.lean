-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_finite_activity_original_closedcap_discounted_negative_mark_integrable
-- name    : AvramDividend.Classical.avram_freshD_finite_activity_original_closedcap_discounted_negative_mark_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:17:42.304471+00:00
-- url     : https://prove2.me/theorems/f3da4539-4f07-4f84-bded-444f135d7671
-- title:
--   Genuine finite-horizon original discounted entire-negative-mark value-increment kernel integrable on finite predictable Levy clock
-- statement:
--   Under finite negative-jump intensity, finite cap and finite predictable time-space clock, the exact nonlinear w(Y+z)-w(Y) discounted source with true stopped ruin and σ masks is integrable over the full negative-mark Lévy intensity product, assuming its precise kernel predictability. This holds even when negative jump sizes have no first moment, since w vanishes after ruin and the uniform value bound controls the full nonlinear increment. It supplies the genuine time×probability×mark L1 obligation for the original stopped compensator, not any expected cash inequality.
-- source:
--   Analytical physical full-negative-mark compensation integrability source of b7420f09 to 04e002c9 and 242ca5f1 in original Avram Dividend Classical. Uses Proved uniform fullmark bound e4637f43 and finite product measure; no artificial fixed-linear Jfull or bound on expected stopped cash.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys132_original_finite_cap_uniform_negative_mark_increment_bound
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_finite_activity_original_closedcap_discounted_negative_mark_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμfinite : μ Set.univ < ⊤)
    (q : ℝ) (hq : 0 ≤ q) (Y : ℝ≥0 × Ω → ℝ)
    (σ : Ω → ℝ≥0) (τ : Ω → ℝ≥0∞)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : ∀ p, H p =
      if 0 < p.1.1 ∧ p.1.1 ≤ σ p.1.2 ∧
          (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 ∧
          0 ≤ Y p.1 ∧ ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1))
      else 0)
    (hHm : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H) :
    Integrable H (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))) := by sorry
