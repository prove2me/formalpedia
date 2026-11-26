-- Prove2me | Theorems.Thm_FD1D_DyadicMass_dyadicTent_scale_left
-- name    : FD1D.DyadicMass.dyadicTent_scale_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:09:46.824555+00:00
-- url     : https://prove2.me/theorems/b2fe2f2d-91c5-50c3-be2f-41b5ef8891ca
-- title:
--   Dyadic Mass: dyadic Tent scale left
-- statement:
--   The Dyadic Mass construction uses the dyadic Tent scale left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1123-L1153
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1123-L1153

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.DyadicMass

theorem FD1D.DyadicMass.dyadicTent_scale_left (l p z : ℝ) (hp : p ≠ 0) :
    dyadicTent (l / 2) (p / 2) z = dyadicTent l p (2 * z) := by sorry
