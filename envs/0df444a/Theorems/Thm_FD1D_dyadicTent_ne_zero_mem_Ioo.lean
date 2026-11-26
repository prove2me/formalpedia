-- Prove2me | Theorems.Thm_FD1D_dyadicTent_ne_zero_mem_Ioo
-- name    : FD1D.dyadicTent_ne_zero_mem_Ioo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:07:56.406167+00:00
-- url     : https://prove2.me/theorems/381a2714-891f-5a04-83e0-5cda4a7bddde
-- title:
--   FD1 D: dyadic Tent ne zero mem Ioo
-- statement:
--   A nonzero tent value lies in the interior of its supporting interval.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L512-L535
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L512-L535

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral

theorem FD1D.dyadicTent_ne_zero_mem_Ioo {l p z : ℝ} (hp : 0 < p)
    (hz : dyadicTent l p z ≠ 0) :
    z ∈ Ioo l (l + p) := by sorry
