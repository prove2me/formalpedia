-- Prove2me | Theorems.Thm_ClassicalComplexWPT_exists_normalizedPreparationSequences
-- name    : ClassicalComplexWPT.exists_normalizedPreparationSequences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:09:38.724274+00:00
-- url     : https://prove2.me/theorems/977d69d8-8043-57ab-bd32-f2931cf91311
-- title:
--   Classical Complex WPT: exists normalized Preparation Sequences
-- statement:
--   Exact order yields a radius and analytic quotient/remainder coefficient
--   maps with the preparation factorization, vanishing origin remainder, and
--   unit-normalized origin quotient.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean#L209-L232
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean#L209-L232

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 5000000
open ClassicalComplexWPT

theorem ClassicalComplexWPT.exists_normalizedPreparationSequences {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) :
    ∃ (r : ℝ≥0) (hr : (r : ℝ≥0∞) < p.radius),
      0 < r ∧ originWeightedCoeffs p r hr d ≠ 0 ∧
      AnalyticAt ℂ (normalizedPreparationQuotient p r hr d) 0 ∧
      AnalyticAt ℂ (normalizedPreparationRemainder p r hr d) 0 ∧
      (∀ᶠ z in 𝓝 (0 : Base n),
        monomialSeq d = convolution (normalizedPreparationQuotient p r hr d z)
            (analyticNormalizedCoefficientMap p r hr d z) +
          normalizedPreparationRemainder p r hr d z ∧
        seqHighShift d (normalizedPreparationRemainder p r hr d z) = 0) ∧
      normalizedPreparationRemainder p r hr d 0 = 0 ∧
      normalizedPreparationQuotient p r hr d 0 0 = 1 := by sorry
