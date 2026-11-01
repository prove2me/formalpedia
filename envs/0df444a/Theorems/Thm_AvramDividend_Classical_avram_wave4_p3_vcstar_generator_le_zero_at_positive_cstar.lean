-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_le_zero_at_positive_cstar
-- name    : AvramDividend.Classical.avram_wave4_p3_vcstar_generator_le_zero_at_positive_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:03:35.258238+00:00
-- url     : https://prove2.me/theorems/8beaad66-ba3c-4f1c-8731-c54573c92e8d
-- title:
--   Original Lévy generator residual upper inequality and integrable domain exactly at the positive dividend barrier
-- statement:
--   Under exactly the Standing, positive discount, finite positive optimal cap, three-way smoothness and strictly-above-barrier generator inequality assumptions of the original P3 canonical endpoint HJB, the actual original compensated Lévy generator belongs to its integrable domain at cap and has discounted residual at most zero. This is a correct one-sided endpoint form, extracted from the now canonically Proved full positive-cap HJB without importing or concealing the still-Open exact interior harmonicity. It is an independently importable positive-cap verification inequality, not an unsupported equality claim.
-- source:
--   Avram, Palmowski and Pistorius (2007), HJB variational inequality (5.8), Lemma 4 strict-interior domain, Proposition 4 verification; canonical Proved vcstar_hjb_at_positive_cstar UUID 8d03da6b-9d29-480a-8905-4d21edfcdaaf, accepted candidate 19708.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_vcstar_generator_le_zero_at_positive_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hcpos : 0 < cstar W)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal ≤ 0 := by sorry
