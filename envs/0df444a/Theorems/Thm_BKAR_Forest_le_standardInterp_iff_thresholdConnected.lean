-- Prove2me | Theorems.Thm_BKAR_Forest_le_standardInterp_iff_thresholdConnected
-- name    : BKAR.Forest.le_standardInterp_iff_thresholdConnected
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:18:08.696089+00:00
-- url     : https://prove2.me/theorems/6cf808b4-129b-5281-8c4c-999e8887a2ae
-- title:
--   Forest: le standard Interp iff threshold Connected
-- statement:
--   For positive thresholds, the standard BKAR edge value is above threshold
--   exactly when its endpoints are threshold-connected.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Threshold.lean#L122-L149
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Threshold.lean#L122-L149

import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_Threshold
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

theorem BKAR.Forest.le_standardInterp_iff_thresholdConnected
    (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (e : Edge V) :
    s ≤ F.standardInterp u e ↔
      F.thresholdConnected u s e.left e.right := by sorry
