-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_xDeg_inr
-- name    : Formalism.CountingSumsFrames.Har2.xDeg_inr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:42.533725+00:00
-- url     : https://prove2.me/theorems/cb325edb-844b-4230-a587-4127ce529ba7
-- title:
--   Har2: x Deg inr
-- statement:
--   The Har2 construction uses the x Deg inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L44-L45

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
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
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}

theorem Formalism.CountingSumsFrames.Har2.xDeg_inr (i : Fin k) : xDeg (Finsupp.single (Sum.inr i : XY k) 1) = 0 := by sorry
