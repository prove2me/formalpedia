-- Prove2me | Theorems.Thm_Formalism_GM_DetBound_norm_det_le_one
-- name    : Formalism.GM.DetBound.norm_det_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:49.25481+00:00
-- url     : https://prove2.me/theorems/add875c3-6ed2-4d78-bd62-163497f05a76
-- title:
--   Det Bound: norm det le one
-- statement:
--   The Det Bound construction uses the norm det le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L98-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L98-L104

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DetBound
open Finset Polynomial
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem Formalism.GM.DetBound.norm_det_le_one {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (hM : ∀ i j, ‖M i j‖ ≤ 1) :
    ‖M.det‖ ≤ 1 := by sorry
