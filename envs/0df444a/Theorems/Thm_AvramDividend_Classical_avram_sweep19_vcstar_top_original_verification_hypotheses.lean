-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep19_vcstar_top_original_verification_hypotheses
-- name    : AvramDividend.Classical.avram_sweep19_vcstar_top_original_verification_hypotheses
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:54:11.49235+00:00
-- url     : https://prove2.me/theorems/dfb75568-fa8e-4951-9edb-54a249dd588e
-- title:
--   Original vcstar top-cap regularity and HJB source conditions
-- statement:
--   For the original spectrally negative Levy process, the root's finite barrier, scale, three-way smoothness and above-barrier generator hypotheses imply the exact source boundary regularity, BV/UBV differentiability on the top-cap region, and global HJB maximum equality required to apply local verification at infinite cap. Derive the regularity from Proved ffdd6f8d and the HJB from Proved edf09308, identifying the finite ofReal top region with the positive half-line. This is the hypothesis package of the unchanged original-process verification route.
-- source:
--   Proved original source vcstar_unrestricted_verification_regularity ffdd6f8d-a5cc-4aee-8726-785404cd72f2 and HJB edf09308-1b7f-449e-ac5d-ae6f22d385c3.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep19_vcstar_top_original_verification_hypotheses
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ContinuousOn (vcstar W) (Ici 0) ∧
    0 ≤ vcstar W 0 ∧
    (∀ y < 0, vcstar W y = 0) ∧
    ((¬ X.BoundedVariation →
      ContDiffOn ℝ 2 (vcstar W)
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) ∧
     (X.BoundedVariation →
      ContDiffOn ℝ 1 (vcstar W)
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)})) ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < (⊤ : ℝ≥0∞) →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0) := by sorry
