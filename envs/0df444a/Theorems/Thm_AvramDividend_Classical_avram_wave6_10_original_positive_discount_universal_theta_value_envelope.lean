-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_positive_discount_universal_theta_value_envelope
-- name    : AvramDividend.Classical.avram_wave6_10_original_positive_discount_universal_theta_value_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:42:15.296236+00:00
-- url     : https://prove2.me/theorems/b8070261-7185-4d4f-a29c-fefe38e511c3
-- title:
--   Any positive discount gives a common exponential bound for every original capped and unrestricted optimal dividend value
-- statement:
--   For the genuine original spectrally negative Lévy process, without Standing or bounded-variation assumptions, any strictly positive q and any reserve x, there exists theta>0 such that both every capped and the unrestricted expected discounted original Stieltjes dividend optimisations obey theta*value≤exp(theta*x). The positive tilt comes from the Proved source psi-continuity/small-tilt theorem, and the bound is the canonically Proved actual-path Chat10 all-cap theta-value inequality. This supplies a uniform cap-independent finite budget useful for dominated localization in the corrected unbounded-variation verification work; it does not prove the arbitrary C² generator martingale formula.
-- source:
--   Source-specific exact consequence of Proved original small positive theta [6b7f5580-f12e-4a18-8862-48af9a18594f] and exact all-cap original-value envelope [24f9b5f0-00d4-4444-bb25-6d3a0cfcdb49], Mathlib 0df444a. Independent of corrected stochastic core 429; no replacement model.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_theta_perpetual_capped_and_unrestricted_value_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_10_original_positive_discount_universal_theta_value_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (x : ℝ) :
    ∃ θ : ℝ, 0 < θ ∧
      (∀ C : ℝ≥0∞,
        ENNReal.ofReal θ * valueFunctionLe X q C x ≤
          ENNReal.ofReal (Real.exp (θ * x))) ∧
      ENNReal.ofReal θ * valueFunction X q x ≤
        ENNReal.ofReal (Real.exp (θ * x)) := by sorry
