-- Prove2me | Theorems.Thm_Formalism_REAL_HWDiag_cov
-- name    : Formalism.REAL.HWDiag_cov
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:20:16.592829+00:00
-- url     : https://prove2.me/theorems/16fbce8e-9310-4176-9641-7251b182da44
-- title:
--   REAL: HWDiag cov
-- statement:
--   The REAL construction uses the HWDiag cov property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/HWDiag.lean#L17-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/HWDiag.lean#L17-L48

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HWDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.HWDiag_cov {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) :
    ∀ (k : ℕ) (a b c d : Fin n),
      E c d * epow E k a b - epow E k a b * E c d =
        (if d = a then epow E k c b else 0) - (if b = c then epow E k a d else 0) := by sorry
