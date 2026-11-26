-- Prove2me | Theorems.Thm_BKAR_Forest_thresholdConnected_iff_exists_le_pathMin
-- name    : BKAR.Forest.thresholdConnected_iff_exists_le_pathMin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:17:41.965591+00:00
-- url     : https://prove2.me/theorems/e689ee90-4aa3-439b-bb38-7af506d63f54
-- title:
--   Forest: threshold Connected iff exists le path Min
-- statement:
--   Threshold connectivity is the same as being in the original forest component
--   with path minimum at least `s`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Threshold.lean#L100-L116
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Threshold.lean#L100-L116

import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_Threshold
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

theorem BKAR.Forest.thresholdConnected_iff_exists_le_pathMin
    (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} (hs : s ≤ 1) (i j : V) :
    F.thresholdConnected u s i j ↔
      ∃ h : F.inSameComponent i j,
        s ≤ F.pathMin u (F.pathInF i j h) := by sorry
