-- Prove2me | Theorems.Thm_ClassicalComplexWPT_eventually_normalizedPreparation_factorization
-- name    : ClassicalComplexWPT.eventually_normalizedPreparation_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:09:18.62335+00:00
-- url     : https://prove2.me/theorems/2168e8ba-133f-56ec-bc0e-b89f23a9491c
-- title:
--   Classical Complex WPT: eventually normalized Preparation factorization
-- statement:
--   The Classical Complex WPT construction uses the eventually normalized Preparation factorization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean#L134-L163
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean#L134-L163

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 5000000
open ClassicalComplexWPT

theorem ClassicalComplexWPT.eventually_normalizedPreparation_factorization {n d : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius)
    (hclose : ‖analyticNormalizedCoefficientMap p r hr d 0 - monomialSeq d‖ <
      (1 : ℝ) / 2) :
    ∀ᶠ z in 𝓝 (0 : Base n),
      monomialSeq d = convolution (normalizedPreparationQuotient p r hr d z)
          (analyticNormalizedCoefficientMap p r hr d z) +
        normalizedPreparationRemainder p r hr d z ∧
      seqHighShift d (normalizedPreparationRemainder p r hr d z) = 0 := by sorry
