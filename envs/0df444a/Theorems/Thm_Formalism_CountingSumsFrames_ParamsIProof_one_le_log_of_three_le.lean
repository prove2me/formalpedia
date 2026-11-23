-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_ParamsIProof_one_le_log_of_three_le
-- name    : Formalism.CountingSumsFrames.ParamsIProof.one_le_log_of_three_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:24.392285+00:00
-- url     : https://prove2.me/theorems/37aa79ff-de36-4382-bac5-e1f9b84c68e7
-- title:
--   Params IProof: one le log of three le
-- statement:
--   The Params IProof construction uses the one le log of three le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/ParamsI.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/ParamsI.lean#L12-L14

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ParamsI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CountingSumsFrames
open Real
open Formalism.CountingSumsFrames.ParamsIProof

theorem Formalism.CountingSumsFrames.ParamsIProof.one_le_log_of_three_le (a : ℝ) (ha : 3 ≤ a) : 1 ≤ Real.log a := by sorry
