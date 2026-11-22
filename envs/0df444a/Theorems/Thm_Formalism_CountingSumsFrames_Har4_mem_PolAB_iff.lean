-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_mem_PolAB_iff
-- name    : Formalism.CountingSumsFrames.Har4.mem_PolAB_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:31:18.88124+00:00
-- url     : https://prove2.me/theorems/4ed444bf-db6b-4151-b8e8-bf2ac62f7d31
-- title:
--   Har4: mem Pol AB iff
-- statement:
--   The Har4 construction uses the mem Pol AB iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L167-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L167-L179

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

theorem Formalism.CountingSumsFrames.Har4.mem_PolAB_iff {K : Type} [Field K] {k A B : ℕ} (f : PolXY K k) :
    f ∈ PolAB K k A B ↔ IsWeightedHomogeneous (wXY k) f (A, B) := by sorry
