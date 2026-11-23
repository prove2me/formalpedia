-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_ctrF_mem_PolAB
-- name    : Formalism.CountingSumsFrames.Har4.ctrF_mem_PolAB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:32.151668+00:00
-- url     : https://prove2.me/theorems/4b96f42d-a534-4457-8d9a-184fc3ac6b81
-- title:
--   Har4: ctr F mem Pol AB
-- statement:
--   The Har4 construction uses the ctr F mem Pol AB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L540-L554
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L540-L554

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
variable {K : Type} [Field K] {k : ℕ}

theorem Formalism.CountingSumsFrames.Har4.ctrF_mem_PolAB {a b : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k a b) :
    ctrF K k f ∈ PolAB K k (a - 1) (b - 1) := by sorry
