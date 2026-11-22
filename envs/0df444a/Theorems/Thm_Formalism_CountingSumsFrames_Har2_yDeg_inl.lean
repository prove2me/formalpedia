-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_yDeg_inl
-- name    : Formalism.CountingSumsFrames.Har2.yDeg_inl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:43.827718+00:00
-- url     : https://prove2.me/theorems/bda50171-fbdc-40cc-9efa-e172928dd168
-- title:
--   Har2: y Deg inl
-- statement:
--   The Har2 construction uses the y Deg inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L42-L43

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

theorem Formalism.CountingSumsFrames.Har2.yDeg_inl (i : Fin k) : yDeg (Finsupp.single (Sum.inl i : XY k) 1) = 0 := by sorry
