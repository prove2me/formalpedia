-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_glAct_glAct_inv
-- name    : Formalism.CountingSumsFrames.Har4.glAct_glAct_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:26.208883+00:00
-- url     : https://prove2.me/theorems/f76728c6-89cb-4f01-9336-4bca901d9c98
-- title:
--   Har4: gl Act gl Act inv
-- statement:
--   The Har4 construction uses the gl Act gl Act inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L149-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L149-L151

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

theorem Formalism.CountingSumsFrames.Har4.glAct_glAct_inv {K : Type} [Field K] {k : ℕ} (g : GL (Fin k) K) (f : PolXY K k) :
    glAct g (glAct g⁻¹ f) = f := by sorry
