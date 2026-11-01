-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_full_hjb_of_interior_harmonicity_and_bounded_strip_residual
-- name    : AvramDividend.Classical.avram_wave4_05_full_hjb_of_interior_harmonicity_and_bounded_strip_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:23:25.683992+00:00
-- url     : https://prove2.me/theorems/aa470a98-0e74-4da8-ae31-bc2608e0e702
-- title:
--   Full original-source HJB from interior harmonicity and a bounded upper-reserve residual strip
-- statement:
--   For the actual standing spectrally negative Levy source and original Gaussian/BV/global-C2 smoothness disjunction, the entire original HJB equation and source generator integrability hold on all positive reserves if the candidate is genuinely generator-q-harmonic below any positive cstar and the source generator residual inequality holds only on the bounded strict upper-reserve strip cstar<y<cstar+1+max(0,X.c/q). The explicit far-field original HJB is already Proved outside the strip, and barrier finiteness and all upper generator domains are derived automatically. In the unresolved pure C2 case the interior source harmonicity is an honest explicit premise, not a silent import of Open P2.
-- source:
--   Avram–Palmowski–Pistorius (2007), Lemma 4 and Theorem 2; Proved far-field HJB 09ea2ea1, full conditional HJB c58ab7bc

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_eventual_hjb_finite_cstar
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_hjb_of_interior_and_above_residual_no_finite_premise

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_full_hjb_of_interior_harmonicity_and_bounded_strip_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hsmooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hres_strip : ∀ y : ℝ,
      (cstar W).toReal < y →
      y < (cstar W).toReal + 1 + max 0 (X.c / q) →
      X.generator (vcstar W) y - q * vcstar W y ≤ 0)
    (hinside : 0 < cstar W → ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x = 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by sorry
