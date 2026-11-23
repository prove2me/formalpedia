-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_mul_mem_PolAB
-- name    : Formalism.CountingSumsFrames.Har4.mul_mem_PolAB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:13.173701+00:00
-- url     : https://prove2.me/theorems/b64a1290-dfc7-4e54-9a49-cbdb560b4cac
-- title:
--   Har4: mul mem Pol AB
-- statement:
--   The Har4 construction uses the mul mem Pol AB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L582-L585
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L582-L585

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

theorem Formalism.CountingSumsFrames.Har4.mul_mem_PolAB {a b a' b' : ℕ} {f f' : PolXY K k} (hf : f ∈ PolAB K k a b)
    (hf' : f' ∈ PolAB K k a' b') : f * f' ∈ PolAB K k (a + a') (b + b') := by sorry
