-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_glAct_mem_PolAB
-- name    : Formalism.CountingSumsFrames.Har4.glAct_mem_PolAB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:31:49.167666+00:00
-- url     : https://prove2.me/theorems/d31a951f-4893-4580-a95a-ebd59560de2e
-- title:
--   Har4: gl Act mem Pol AB
-- statement:
--   The Har4 construction uses the gl Act mem Pol AB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L181-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L181-L216

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

theorem Formalism.CountingSumsFrames.Har4.glAct_mem_PolAB {K : Type} [Field K] {k A B : ℕ} (g : GL (Fin k) K) (f : PolXY K k)
    (hf : f ∈ PolAB K k A B) : glAct g f ∈ PolAB K k A B := by sorry
