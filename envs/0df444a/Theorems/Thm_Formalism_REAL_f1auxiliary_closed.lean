-- Prove2me | Theorems.Thm_Formalism_REAL_f1auxiliary_closed
-- name    : Formalism.REAL.f1auxiliary_closed
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:21:04.097752+00:00
-- url     : https://prove2.me/theorems/88cf914c-08f8-4efa-a26a-90e6e1c3de7a
-- title:
--   REAL: f1auxiliary closed
-- statement:
--   The REAL construction uses the f1auxiliary closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexificationHolds.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexificationHolds.lean#L49-L51

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

theorem Formalism.REAL.f1auxiliary_closed {n : ℕ} (ε : Fin n → Bool) : IsClosed {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g} := by sorry
