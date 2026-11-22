-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_yDeg_add
-- name    : Formalism.CountingSumsFrames.Har2.yDeg_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:12.652011+00:00
-- url     : https://prove2.me/theorems/3338586a-c3ad-4939-b44a-e88082ac96c8
-- title:
--   Har2: y Deg add
-- statement:
--   The Har2 construction uses the y Deg add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L38-L39

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

theorem Formalism.CountingSumsFrames.Har2.yDeg_add (m m' : XY k →₀ ℕ) : yDeg (m + m') = yDeg m + yDeg m' := by sorry
