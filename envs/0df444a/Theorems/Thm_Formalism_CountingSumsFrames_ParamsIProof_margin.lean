-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_ParamsIProof_margin
-- name    : Formalism.CountingSumsFrames.ParamsIProof.margin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:38.798217+00:00
-- url     : https://prove2.me/theorems/a4a2158e-40ed-4672-8df6-3fc87ec13c90
-- title:
--   Params IProof: margin
-- statement:
--   The Params IProof construction uses the margin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/ParamsI.lean#L16-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/ParamsI.lean#L16-L65

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

theorem Formalism.CountingSumsFrames.ParamsIProof.margin (C Cm N1 k Q c La b' Ib X Nr Y : ℝ)
    (hCm : 1 ≤ Cm) (hC : 1000 * Cm ≤ C) (hN1 : 1 ≤ N1) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (hLa : 1 ≤ La) (hIb : 0 ≤ Ib) (hb : 0 < b') (hc0 : 0 ≤ c) (hc : c ≤ 4 * X) (hX : 0 ≤ X)
    (hN : 1 ≤ Nr) (hY : 1 ≤ Y) (hb' : C * k ^ 3 * Nr * Q ^ 4 * X * Y ≤ b') :
    ∀ Ai : ℝ, b' / (2 * Q) ≤ Ai →
      2 * (Cm * k * N1 * Q * c) + 12 * c ≤ (C * N1 * La / k + 2 * Ib / b') * Ai / 4 := by sorry
