-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_hjb_of_interior_and_above_residual
-- name    : AvramDividend.Classical.avram_wave4_05_hjb_of_interior_and_above_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:24:29.841881+00:00
-- url     : https://prove2.me/theorems/91a66237-633a-4eb5-ac1e-abd1ba230ed8
-- title:
--   Original Lévy full HJB from interior harmonicity and above-barrier residual alone
-- statement:
--   For the original standing spectrally negative Levy process and q-scale function with finite cstar, exact original smoothness alternatives, a nonpositive generator residual strictly above cstar, and the exact source interior generator equation below positive cstar, the complete HJB holds at every positive reserve. Above-barrier GeneratorIntegrable is derived from the canonically Proved unconditional source theorem vcstar_generatorIntegrable_strictly_above_real_cstar, and the full original HJB split follows from the canonically Proved avram_wave4_05_full_hjb_from_interior_harmonicity. This removes an otherwise redundant upper generator-domain hypothesis, without assuming the still Open pure-jump interior harmonicity.
-- source:
--   Original Avram-Palmowski-Pistorius (2007) generator and HJB, Proved source above-barrier integrability 32cfe60b and accepted conditional HJB 8915fbc2

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_full_hjb_from_interior_harmonicity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Original source HJB with above-generator integrability derived rather than assumed. -/

theorem AvramDividend.Classical.avram_wave4_05_hjb_of_interior_and_above_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hres_above : ∀ y : ℝ, (cstar W).toReal < y →
      X.generator (vcstar W) y - q * vcstar W y ≤ 0)
    (hinside : 0 < cstar W → ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x = 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by sorry
