-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_ParamsIProof_share
-- name    : Formalism.CountingSumsFrames.ParamsIProof.share
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:27.464401+00:00
-- url     : https://prove2.me/theorems/0be65340-d8e0-4016-88ec-4570bab58f40
-- title:
--   Params IProof: share
-- statement:
--   The Params IProof construction uses the share property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/ParamsI.lean#L67-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/ParamsI.lean#L67-L110

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

theorem Formalism.CountingSumsFrames.ParamsIProof.share (C k Y M a b' Ib Yb Nr La L : ℝ) (hC : 2 ≤ C) (hk : 2 ≤ k) (hY : 1 ≤ Y)
    (hM0 : 0 ≤ M) (hM : C * k ^ 3 * Y * M ≤ b') (hb : 0 < b') (hYb : 1 ≤ Yb) (hN : 1 ≤ Nr)
    (hLa : 1 ≤ La) (hL : 1 ≤ L) (ha : k * Y ^ 2 * Yb * Nr * La * L ≤ a / b')
    (hIb : Yb * Nr * La * b' / k ≤ Ib) : M * (k * Y / a + 1 / Ib) ≤ 1 / Y := by sorry
