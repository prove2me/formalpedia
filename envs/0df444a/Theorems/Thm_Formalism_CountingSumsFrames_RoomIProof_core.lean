-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_RoomIProof_core
-- name    : Formalism.CountingSumsFrames.RoomIProof.core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:45:41.24561+00:00
-- url     : https://prove2.me/theorems/1a9e7a5b-6962-452c-a7b4-8f50418328bd
-- title:
--   Room IProof: core
-- statement:
--   The Room IProof construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/IntervalRoomBound.lean#L12-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/IntervalRoomBound.lean#L12-L62

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_EdgeSumGoodRank
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_IntervalRoomBound
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
open Formalism.CountingSumsFrames.RoomIProof

theorem Formalism.CountingSumsFrames.RoomIProof.core (C Cm N1 k Q c La b' Ib X Nr Y Yb : ℝ)
    (hCm : 0 ≤ Cm) (hC : 192 + 32 * Cm ≤ C) (hN1 : 1 ≤ N1) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (hLa : N1 ^ 2 ≤ La) (hYb : C ≤ Yb) (hb : 0 < b') (hc0 : 0 ≤ c) (hc : c ≤ 4 * X) (hX : 0 ≤ X)
    (hN : 1 ≤ Nr) (hY : 1 ≤ Y) (hb' : C * k ^ 3 * Nr * Q ^ 4 * X * Y ≤ b')
    (hIb : Yb * Nr * La * b' / k ≤ Ib) :
    12 * c + (N1 + 1) * (Cm * k * N1 * Q * c) ≤ (2 * Ib / b') * (b' / (2 * Q)) / 4 := by sorry
