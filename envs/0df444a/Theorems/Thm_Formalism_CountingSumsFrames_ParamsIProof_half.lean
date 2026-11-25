-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_ParamsIProof_half
-- name    : Formalism.CountingSumsFrames.ParamsIProof.half
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:24:06.500595+00:00
-- url     : https://prove2.me/theorems/53956fd2-aebb-4e91-ba63-908ba3fb2cdd
-- title:
--   Params IProof: half
-- statement:
--   The Params IProof construction uses the half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/ParamsI.lean#L155-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/ParamsI.lean#L155-L169

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

theorem Formalism.CountingSumsFrames.ParamsIProof.half (Yb : ℝ) (N : ℕ) (hYb : 4 ≤ Yb) (hN : 1 ≤ N) :
    1 / 2 ≤ (1 - 2 / (Yb * N)) ^ N := by sorry
