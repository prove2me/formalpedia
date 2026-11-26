-- Prove2me | Theorems.Thm_ClassicalComplexWPT_preparation_factorization_of_sequence_factorization
-- name    : ClassicalComplexWPT.preparation_factorization_of_sequence_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:12:55.904665+00:00
-- url     : https://prove2.me/theorems/e14cb439-3783-48af-940f-08010a4473eb
-- title:
--   Classical Complex WPT: preparation factorization of sequence factorization
-- statement:
--   Pointwise reconstruction once sequence division and convergence are
--   available.  Keeping the convergence hypotheses explicit makes this lemma
--   reusable for both the public existence and uniqueness arguments.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L154-L209
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L154-L209

import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Definitions.Def_ClassicalComplexWPT_PublicExistence
set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT

theorem ClassicalComplexWPT.preparation_factorization_of_sequence_factorization {n d : ℕ}
    {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (hr0 : 0 < r)
    (htop : originWeightedCoeffs p r hr d ≠ 0)
    (z : Base n) (w : ℂ)
    (hfac : monomialSeq d =
      convolution (normalizedPreparationQuotient p r hr d z)
        (analyticNormalizedCoefficientMap p r hr d z) +
          normalizedPreparationRemainder p r hr d z)
    (hsupp : seqHighShift d (normalizedPreparationRemainder p r hr d z) = 0)
    (hw : ‖(r : ℂ)⁻¹ * w‖ < 1)
    (hrecon : evalL1PowerSeries ((weightedCoefficientSeries p r).sum z)
        ((r : ℂ)⁻¹ * w) = f (z, w))
    (hQne : preparationQuotientEval p r hr d (z, w) ≠ 0) :
    f (z, w) = preparationUnit p r hr d (z, w) *
      preparedPolynomial d (preparationCoefficient p r hr d) (z, w) := by sorry
