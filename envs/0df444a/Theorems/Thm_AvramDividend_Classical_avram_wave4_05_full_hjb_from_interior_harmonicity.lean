-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_full_hjb_from_interior_harmonicity
-- name    : AvramDividend.Classical.avram_wave4_05_full_hjb_from_interior_harmonicity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:05:41.793324+00:00
-- url     : https://prove2.me/theorems/8915fbc2-bf68-4bce-9131-c4369d0c6e33
-- title:
--   Original source full HJB from exact interior compensated generator harmonicity and verified cap
-- statement:
--   Under the exact Standing spectrally negative Levy process, q-scale W, finite optimal barrier, the original Gaussian/BV/global-C2 regularity alternatives, original upper-reserve generator domain and nonpositive residual, and an explicit conditional source interior generator harmonicity premise when the barrier is positive, the full HJB holds at every positive reserve. This theorem uses the now canonically Proved endpoint HJB theorem and original derivative, above-barrier and zero-barrier results. The explicit interior premise is mathematically indispensable until the independently owned pure-jump q-scale generator harmonicity has been Proved.
-- source:
--   Original Avram-Palmowski-Pistorius (2007) generator/HJB, exact verified endpoint 8d03da6b and source interior equation 88d146b8

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_at_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_above_cstar_of_generator
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator_zero_barrier

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Full HJB from the source interior generator identity, the verified cap and the given upper generator inequality. -/

theorem AvramDividend.Classical.avram_wave4_05_full_hjb_from_interior_harmonicity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0)
    (hinside : 0 < cstar W → ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x = 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by sorry
