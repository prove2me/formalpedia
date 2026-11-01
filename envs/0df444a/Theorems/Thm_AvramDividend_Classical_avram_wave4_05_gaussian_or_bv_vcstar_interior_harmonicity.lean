-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_or_bv_vcstar_interior_harmonicity
-- name    : AvramDividend.Classical.avram_wave4_05_gaussian_or_bv_vcstar_interior_harmonicity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:26:02.076762+00:00
-- url     : https://prove2.me/theorems/e9e1107a-9b16-4600-ac27-bee03dea3d5f
-- title:
--   Actual optimal-barrier generator is q-harmonic under Gaussian or bounded variation
-- statement:
--   At every reserve strictly between zero and the positive optimal barrier, the actual original Lévy generator has integrable compensated jump kernel and annihilates the scale-normalised barrier value after discounting, under exactly the Gaussian-or-bounded-variation disjunction. This combines two canonically Proved full source branch theorems, keeping the pure unbounded-variation no-Gaussian C2 branch for the separate owner.
-- source:
--   Canonical Gaussian interior generator theorem 01079aa0 and BV unconditional interior source generator theorem b196c9ff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_vcstar_interior_harmonicity
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero_bv_unconditional_20261026
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Original interior compensated generator, both canonically solved branches. -/

theorem AvramDividend.Classical.avram_wave4_05_gaussian_or_bv_vcstar_interior_harmonicity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hbranch : 0 < X.σ ∨ X.BoundedVariation)
    (hc : 0 < cstar W) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x = 0 := by sorry
