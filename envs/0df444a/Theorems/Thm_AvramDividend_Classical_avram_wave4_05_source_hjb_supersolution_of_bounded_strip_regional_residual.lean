-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_hjb_supersolution_of_bounded_strip_regional_residual
-- name    : AvramDividend.Classical.avram_wave4_05_source_hjb_supersolution_of_bounded_strip_regional_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:24:20.980582+00:00
-- url     : https://prove2.me/theorems/47638a97-172f-4588-9159-9357867ec1f6
-- title:
--   Full original-source HJB supersolution from interior superharmonicity and bounded upper-reserve residual strip
-- statement:
--   For an original standing spectrally negative Levy source with q>0, genuine q-scale function and original Gaussian/BV/global-C2 smoothness alternative, a global compensated-generator HJB supersolution and domain are obtained from mere source interior generator superharmonicity on any nonempty continuation region and the upper generator residual inequality only on the bounded interval cstar<y<cstar+1+max(0,X.c/q). At and beyond the explicit threshold, the exact source far-field HJB is already Proved. The new result does not require interior harmonic equality, barrier finiteness, or upper-domain integrability as hypotheses, and is a direct analytic interface for stochastic verification without importing the still Open P2 pure-jump harmonicity.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4 HJB supersolution; source supersolution 4de732b5 and far HJB 09ea2ea1

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_eventual_hjb_finite_cstar
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_original_source_hjb_supersolution_of_interior_superharmonicity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_hjb_supersolution_of_bounded_strip_regional_residual
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
    (hinside_super : 0 < cstar W → ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) ≤ 0 := by sorry
