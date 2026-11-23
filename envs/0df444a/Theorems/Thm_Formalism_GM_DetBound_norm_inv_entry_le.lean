-- Prove2me | Theorems.Thm_Formalism_GM_DetBound_norm_inv_entry_le
-- name    : Formalism.GM.DetBound.norm_inv_entry_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:15.590027+00:00
-- url     : https://prove2.me/theorems/9d129ad9-da39-465f-82e9-71a756d01824
-- title:
--   Det Bound: norm inv entry le
-- statement:
--   The Det Bound construction uses the norm inv entry le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L106-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L106-L115

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

theorem Formalism.GM.DetBound.norm_inv_entry_le {n : ℕ} (U : Matrix (Fin n) (Fin n) K) (hU : ∀ i j, ‖U i j‖ ≤ 1)
    (hdet : ‖U.det‖ = 1) (i j : Fin n) : ‖U⁻¹ i j‖ ≤ 1 := by sorry
