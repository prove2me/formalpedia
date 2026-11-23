-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_ParamsIProof_cnkc
-- name    : Formalism.CountingSumsFrames.ParamsIProof.cnkc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:32.3448+00:00
-- url     : https://prove2.me/theorems/6c6194bb-b2cd-42b2-bf71-92f9a9bb126b
-- title:
--   Params IProof: cnkc
-- statement:
--   The Params IProof construction uses the cnkc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/ParamsI.lean#L112-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/ParamsI.lean#L112-L120

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

theorem Formalism.CountingSumsFrames.ParamsIProof.cnkc (C Ck k Y Nr cl b' : ℝ) (hCk : 1 ≤ Ck) (hC : 1000 * Ck ≤ C) (hk : 1 ≤ k) (hY : 1 ≤ Y)
    (hN : 0 ≤ Nr) (hcl : 0 ≤ cl) (hb : 0 < b') (hM : C * k ^ 3 * Y * (Nr * cl) ≤ b') :
    Ck * Nr * k * (2 * cl) / b' ≤ 1 / Y := by sorry
