-- Prove2me | Theorems.Thm_FD1D_DyadicMass_dyadicTent_scale_right
-- name    : FD1D.DyadicMass.dyadicTent_scale_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:09:51.562708+00:00
-- url     : https://prove2.me/theorems/fcd27496-3d62-5a27-9ea4-b03917b53a3a
-- title:
--   Dyadic Mass: dyadic Tent scale right
-- statement:
--   The Dyadic Mass construction uses the dyadic Tent scale right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1155-L1193
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1155-L1193

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.DyadicMass

theorem FD1D.DyadicMass.dyadicTent_scale_right (l p z : ℝ) (hp : p ≠ 0) :
    dyadicTent (1 / 2 + l / 2) (p / 2) z =
      dyadicTent l p (2 * z - 1) := by sorry
