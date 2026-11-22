-- Prove2me | Theorems.Thm_Formalism_REAL_continuous_hs_real_place_taylor
-- name    : Formalism.REAL.continuous_hs_real_place_taylor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:52:09.478795+00:00
-- url     : https://prove2.me/theorems/d02b60a8-72c7-49b3-96e8-9de05ff7d837
-- title:
--   REAL: continuous hs real place taylor
-- statement:
--   The REAL construction uses the continuous hs real place taylor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexificationHolds.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexificationHolds.lean#L29-L32

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.continuous_hs_real_place_taylor {n : ℕ} : Continuous (hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := by sorry
