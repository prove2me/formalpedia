-- Prove2me | Theorems.Thm_Formalism_REAL_f1auxiliary_hs_one
-- name    : Formalism.REAL.f1auxiliary_hs_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:36:02.89754+00:00
-- url     : https://prove2.me/theorems/efeabd3f-22fe-4c44-a8d0-239dee81a1dc
-- title:
--   REAL: f1auxiliary hs one
-- statement:
--   The REAL construction uses the f1auxiliary hs one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexificationHolds.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexificationHolds.lean#L34-L40

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

theorem Formalism.REAL.f1auxiliary_hs_one (n : ℕ) : hs (1 : Matrix (Fin n) (Fin n) ℂ) = n := by sorry
