-- Prove2me | Theorems.Thm_FD1D_dyadicTent_eq_zero_of_not_mem
-- name    : FD1D.dyadicTent_eq_zero_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:08:11.461295+00:00
-- url     : https://prove2.me/theorems/8335fa46-0d75-5384-98ba-d5f0addbc94b
-- title:
--   FD1 D: dyadic Tent eq zero of not mem
-- statement:
--   The FD1 D construction uses the dyadic Tent eq zero of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L498-L509
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L498-L509

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral

theorem FD1D.dyadicTent_eq_zero_of_not_mem {l p z : ℝ} (hp : 0 ≤ p)
    (hz : z ∉ Icc l (l + p)) :
    dyadicTent l p z = 0 := by sorry
