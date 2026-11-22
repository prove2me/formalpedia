-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_glAct_hXY
-- name    : Formalism.CountingSumsFrames.Har4.glAct_hXY
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:35:00.713864+00:00
-- url     : https://prove2.me/theorems/0abc92a5-bf39-410c-bc63-e5f63fadb76f
-- title:
--   Har4: gl Act h XY
-- statement:
--   The Har4 construction uses the gl Act h XY property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L76-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L76-L102

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

theorem Formalism.CountingSumsFrames.Har4.glAct_hXY {K : Type} [Field K] {k : ℕ} (g : GL (Fin k) K) : glAct g (hXY K k) = hXY K k := by sorry
