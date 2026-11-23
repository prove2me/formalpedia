-- Prove2me | Theorems.Thm_Formalism_GM_DetBound_gaussR_det_le
-- name    : Formalism.GM.DetBound.gaussR_det_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:16.514172+00:00
-- url     : https://prove2.me/theorems/fbb5a650-ed31-4b0a-be50-3310038bda6c
-- title:
--   Det Bound: gauss R det le
-- statement:
--   The Det Bound construction uses the gauss R det le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L74-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L74-L86

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

theorem Formalism.GM.DetBound.gaussR_det_le (ρ : NNReal) {n : ℕ} (M : Matrix (Fin n) (Fin n) K[X]) (b : Fin n → NNReal)
    (hb : ∀ i j, gaussR ρ (M i j) ≤ b i) : gaussR ρ M.det ≤ ∏ i, b i := by sorry
