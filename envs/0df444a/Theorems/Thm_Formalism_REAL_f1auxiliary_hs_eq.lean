-- Prove2me | Theorems.Thm_Formalism_REAL_f1auxiliary_hs_eq
-- name    : Formalism.REAL.f1auxiliary_hs_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:21:06.478445+00:00
-- url     : https://prove2.me/theorems/0e519905-64e9-4f07-9414-bbe8e5a37962
-- title:
--   REAL: f1auxiliary hs eq
-- statement:
--   The REAL construction uses the f1auxiliary hs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexificationHolds.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexificationHolds.lean#L22-L27

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

theorem Formalism.REAL.f1auxiliary_hs_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : hs g = (trace (gᴴ * g)).re := by sorry
