-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_ParamsIProof_sumP
-- name    : Formalism.CountingSumsFrames.ParamsIProof.sumP
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:24:03.306839+00:00
-- url     : https://prove2.me/theorems/2eeddc6d-328c-4e12-88c6-9be86ddc0c22
-- title:
--   Params IProof: sum P
-- statement:
--   The Params IProof construction uses the sum P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/ParamsI.lean#L122-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/ParamsI.lean#L122-L153

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

theorem Formalism.CountingSumsFrames.ParamsIProof.sumP (k Y Yb Nr La L a b' : ℝ) (hk : 1 ≤ k) (hY : 1 ≤ Y) (hYb : 1 ≤ Yb) (hN : 1 ≤ Nr)
    (hLa : 0 ≤ La) (hL : 1 ≤ L) (hb : 0 < b') (ha0 : 0 < a)
    (ha : k * Y ^ 2 * Yb * Nr * La * L ≤ a / b')
    (hexp : Real.exp (-La / 3) ≤ 1 / a) (hYbNa : Yb * Nr ≤ a) :
    ∀ al : ℝ, a ≤ al →
      1 - 2 / (Yb * Nr) ≤ (1 - (k - 1) * (La * b' / k) / al) * (1 - Real.exp (-La / 3)) := by sorry
