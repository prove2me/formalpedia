-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_coeff_mem_of_h_pow_mul
-- name    : Formalism.CountingSumsFrames.Har4.coeff_mem_of_h_pow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:43.175171+00:00
-- url     : https://prove2.me/theorems/49c27260-0f1e-4545-b2c9-ce7b830c1752
-- title:
--   Har4: coeff mem of h pow mul
-- statement:
--   The Har4 construction uses the coeff mem of h pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L439-L445
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L439-L445

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har4

theorem Formalism.CountingSumsFrames.Har4.coeff_mem_of_h_pow_mul {K : Type} [Field K] {k : ℕ} (R : Subring K) (i0 : Fin k) (j : ℕ)
    (G : PolXY K k) (hG : hXY K k ^ j * G ∈ GaussLat R) : G ∈ GaussLat R := by sorry
