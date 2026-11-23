-- Prove2me | Theorems.Thm_Formalism_REAL_f1auxiliary_entry_le
-- name    : Formalism.REAL.f1auxiliary_entry_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:18.700887+00:00
-- url     : https://prove2.me/theorems/fb78fcdc-622c-4f33-b4cf-b22b08de96dc
-- title:
--   REAL: f1auxiliary entry le
-- statement:
--   The REAL construction uses the f1auxiliary entry le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexificationHolds.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexificationHolds.lean#L53-L59

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

theorem Formalism.REAL.f1auxiliary_entry_le {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖g i j‖ ^ 2 ≤ hs g := by sorry
