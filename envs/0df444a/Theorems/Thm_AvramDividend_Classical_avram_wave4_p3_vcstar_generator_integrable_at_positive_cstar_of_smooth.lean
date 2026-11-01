-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_integrable_at_positive_cstar_of_smooth
-- name    : AvramDividend.Classical.avram_wave4_p3_vcstar_generator_integrable_at_positive_cstar_of_smooth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:01:29.901235+00:00
-- url     : https://prove2.me/theorems/0c561a07-1b88-48bf-969f-1f97225c21f1
-- title:
--   Exact source generator domain at a finite positive optimal dividend cap under every canonical smoothness branch
-- statement:
--   Without assuming generator harmonicity or generator inequalities away from the cap, the actual candidate vcstar belongs to the source compensated Levy generator domain at the strictly positive finite cap whenever the paper's canonical positive-volatility, bounded-variation, or full positive-state C² alternative holds. This independently closes the generator-domain conjunct common to the original positive-cap exact generator theorem 91803827 and HJB theorem 8d03da6b, by combining the individually canonically Proved Gaussian/BV endpoint generator identity and global-C² endpoint compensated-integrability results.
-- source:
--   Avram, Palmowski, Pistorius (2007), source compensated generator at positive optimal dividend cap; Proved P3 Gaussian/BV exact endpoint d2afd925-cf25-42e0-a0d1-96ba9cc7383d and 05A pure C2 endpoint domain fbf83acf-1bfd-45ee-8c96-930992cc1901. Canonical primary endpoint 91803827 remains P3-only.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_vcstar_generator_integrable_at_positive_cstar_of_smooth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal := by sorry
