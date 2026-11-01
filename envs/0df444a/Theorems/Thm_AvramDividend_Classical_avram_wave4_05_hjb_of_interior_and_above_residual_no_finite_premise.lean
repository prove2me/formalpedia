-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_hjb_of_interior_and_above_residual_no_finite_premise
-- name    : AvramDividend.Classical.avram_wave4_05_hjb_of_interior_and_above_residual_no_finite_premise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:35:02.48502+00:00
-- url     : https://prove2.me/theorems/c58ab7bc-b738-44b3-a9d3-2b2ca76a2a76
-- title:
--   Full original-source barrier HJB from interior harmonicity and above-cap residual with automatic barrier finiteness
-- statement:
--   For an actual standing spectrally negative Lévy source and positive discount, assume the original Gaussian/BV/C2 alternative, compensated local q-harmonicity of the candidate in any nonempty interior barrier strip, and only the above-cap generator residual inequality. Then every positive reserve is in the actual source generator domain and satisfies the complete HJB. The original standing scale function already forces finite cstar, and upper-domain integrability follows from the scale source theorem; neither is assumed separately.
-- source:
--   Avram–Palmowski–Pistorius (2007), Lemma 4; canonical source HJB 91a66237 and cstar_lt_top 7bb43015

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_hjb_of_interior_and_above_residual

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_hjb_of_interior_and_above_residual_no_finite_premise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hsmooth : 0 < X.σ ∨ X.BoundedVariation ∨
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
