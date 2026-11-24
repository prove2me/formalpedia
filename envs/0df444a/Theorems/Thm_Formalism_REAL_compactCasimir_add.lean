-- Prove2me | Theorems.Thm_Formalism_REAL_compactCasimir_add
-- name    : Formalism.REAL.compactCasimir_add
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:20:21.157825+00:00
-- url     : https://prove2.me/theorems/53aa5463-1f17-462a-a39e-61d97ee246c7
-- title:
--   REAL: compact Casimir add
-- statement:
--   The REAL construction uses the compact Casimir add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L140-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L140-L160

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ}

theorem Formalism.REAL.compactCasimir_add (ε : Fin n → Bool) (S P : Fin n → Fin n → Module.End ℂ W)
    (hc : ∀ a b c d, S a b * P c d = P c d * S a b) :
    CasK ε (fun a b => S a b + P a b) = CasK ε S + CasK ε P +
      2 * ∑ a, ∑ b, (if ε a = ε b then S a b * P b a else 0) := by sorry
