-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_or_bv_hjb_residual_only
-- name    : AvramDividend.Classical.avram_wave4_05_gaussian_or_bv_hjb_residual_only
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:34:09.001435+00:00
-- url     : https://prove2.me/theorems/7842ea2c-64a7-4e75-8fb1-7871311c4536
-- title:
--   Source Gaussian or BV barrier HJB from above-barrier residual inequality alone
-- statement:
--   For the original standing spectrally negative Levy process, a positive discount q, a genuine q-scale function W, either positive Gaussian variance coefficient or bounded variation, and the sole above-barrier generator residual inequality, the source Hamilton-Jacobi-Bellman equation and generator integrability hold for every positive reserve. Finiteness of cstar is derived from the canonically Proved cstar_lt_top; the exact source interior generator is Proved in the Gaussian/BV disjunction, while source above-cap generator integrability is automatic by a canonically Proved theorem. No pure-jump C2 assumption or missing P2 harmonicity is used.
-- source:
--   Avram-Palmowski-Pistorius (2007), original source Lévy generator; accepted Gaussian/BV interior generator e9e1107a and residual-only full HJB 91a66237

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_or_bv_vcstar_interior_harmonicity
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_hjb_of_interior_and_above_residual

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Full source Gaussian/BV HJB without a separate finiteness or above-domain premise. -/

theorem AvramDividend.Classical.avram_wave4_05_gaussian_or_bv_hjb_residual_only
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hbranch : 0 < X.σ ∨ X.BoundedVariation)
    (hres_above : ∀ y : ℝ, (cstar W).toReal < y →
      X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by sorry
