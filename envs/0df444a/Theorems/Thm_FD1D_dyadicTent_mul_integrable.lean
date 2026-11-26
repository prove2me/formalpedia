-- Prove2me | Theorems.Thm_FD1D_dyadicTent_mul_integrable
-- name    : FD1D.dyadicTent_mul_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:08:34.787798+00:00
-- url     : https://prove2.me/theorems/e563d809-dc81-4cf5-bd23-007751c7ae71
-- title:
--   FD1 D: dyadic Tent mul integrable
-- statement:
--   The FD1 D construction uses the dyadic Tent mul integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L670-L675
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L670-L675

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral

theorem FD1D.dyadicTent_mul_integrable (l₁ p₁ l₂ p₂ : ℝ) (hp₁ : 0 < p₁) :
    Integrable (fun z => dyadicTent l₁ p₁ z * dyadicTent l₂ p₂ z) := by sorry
