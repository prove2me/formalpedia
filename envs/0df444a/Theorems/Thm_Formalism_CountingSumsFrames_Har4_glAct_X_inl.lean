-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_glAct_X_inl
-- name    : Formalism.CountingSumsFrames.Har4.glAct_X_inl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:35:17.75777+00:00
-- url     : https://prove2.me/theorems/bbfeb657-0a11-4f58-ad1a-ea9b59244952
-- title:
--   Har4: gl Act X inl
-- statement:
--   The Har4 construction uses the gl Act X inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L67-L69

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

theorem Formalism.CountingSumsFrames.Har4.glAct_X_inl {K : Type} [Field K] {k : ℕ} (g : GL (Fin k) K) (i : Fin k) :
    glAct g (X (Sum.inl i)) = ∑ j : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) * X (Sum.inl j) := by sorry
