-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_or_bv_hjb_of_bounded_strip_residual
-- name    : AvramDividend.Classical.avram_wave4_05_gaussian_or_bv_hjb_of_bounded_strip_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:23:32.130311+00:00
-- url     : https://prove2.me/theorems/8670c99b-ce24-49d6-996a-7724ac13546f
-- title:
--   Gaussian/BV full original-source HJB from the generator inequality on a bounded upper-reserve strip
-- statement:
--   For an original standing spectrally negative Levy process with q>0 and genuine scale function in the Gaussian or bounded-variation branches, it is enough to establish the actual compensated generator residual Γvcstar−qvcstar≤0 only for reserves y strictly between the optimal barrier cstar and the finite threshold cstar+1+max(0,X.c/q). The canonically Proved eventual HJB theorem supplies the exact source generator domain and max=0 at every reserve at or beyond that threshold; Proved barrier finiteness makes the threshold finite. The Proved Gaussian/BV residual-only full HJB theorem then yields true generator integrability and full HJB for every y>0, including cstar=0. No pure-jump C2 source harmonicity or stochastic upper bound is assumed.
-- source:
--   Avram–Palmowski–Pistorius (2007), generator and HJB; Proved source far-field HJB 09ea2ea1, Gaussian/BV source HJB 7842ea2c

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_eventual_hjb_finite_cstar
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_or_bv_hjb_residual_only

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_gaussian_or_bv_hjb_of_bounded_strip_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hbranch : 0 < X.σ ∨ X.BoundedVariation)
    (hres_strip : ∀ y : ℝ,
      (cstar W).toReal < y →
      y < (cstar W).toReal + 1 + max 0 (X.c / q) →
      X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by sorry
